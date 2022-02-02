/*-------------------------------------------------------------------------
 *
 * printtup.c
 *	  Routines to print out tuples to the destination (both frontend
 *	  clients and standalone backends are supported here).
 *
 *
 * Portions Copyright (c) 1996-2021, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/access/common/printtup.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/printtup.h"
#include "libpq/libpq.h"
#include "libpq/pqformat.h"
#include "tcop/pquery.h"
#include "utils/lsyscache.h"
#include "utils/memdebug.h"
#include "utils/memutils.h"

#include <snappy-c.h>
#include <zstd.h>
#include <time.h>

static void printtup_startup(DestReceiver *self, int operation,
							 TupleDesc typeinfo);
static bool printtup(TupleTableSlot *slot, DestReceiver *self);
static void printtup_shutdown(DestReceiver *self);
static void printtup_destroy(DestReceiver *self);

/* ----------------------------------------------------------------
 *		printtup / debugtup support
 * ----------------------------------------------------------------
 */

/* ----------------
 *		Private state for a printtup destination object
 *
 * NOTE: finfo is the lookup info for either typoutput or typsend, whichever
 * we are using for this column.
 * ----------------
 */
typedef struct
{								/* Per-attribute information */
	Oid			typoutput;		/* Oid for the type's text output fn */
	Oid			typsend;		/* Oid for the type's binary output fn */
	bool		typisvarlena;	/* is it varlena (ie possibly toastable)? */
	int16		format;			/* format code for this column */
	FmgrInfo	finfo;			/* Precomputed call info for output fn */
} PrinttupAttrInfo;

typedef struct
{
	DestReceiver pub;			/* publicly-known function pointers */
	Portal		portal;			/* the Portal we are printing from */
	bool		sendDescrip;	/* send RowDescription at startup? */
	TupleDesc	attrinfo;		/* The attr info we are set up for */
	int			nattrs;
	PrinttupAttrInfo *myinfo;	/* Cached info about each attr */
	StringInfoData buf;			/* output buffer (*not* in tmpcontext) */
	MemoryContext tmpcontext;	/* Memory context for per-row workspace */
} DR_printtup;

/* ----------------
 *		Initialize: create a DestReceiver for printtup
 * ----------------
 */
DestReceiver *
printtup_create_DR(CommandDest dest)
{
	DR_printtup *self = (DR_printtup *) palloc0(sizeof(DR_printtup));

	self->pub.receiveSlot = printtup;	/* might get changed later */
	self->pub.rStartup = printtup_startup;
	self->pub.rShutdown = printtup_shutdown;
	self->pub.rDestroy = printtup_destroy;
	self->pub.mydest = dest;

	/*
	 * Send T message automatically if DestRemote, but not if
	 * DestRemoteExecute
	 */
	self->sendDescrip = (dest == DestRemote);

	self->attrinfo = NULL;
	self->nattrs = 0;
	self->myinfo = NULL;
	self->buf.data = NULL;
	self->tmpcontext = NULL;

	return (DestReceiver *) self;
}

/*
 * Set parameters for a DestRemote (or DestRemoteExecute) receiver
 */
void
SetRemoteDestReceiverParams(DestReceiver *self, Portal portal)
{
	DR_printtup *myState = (DR_printtup *) self;

	Assert(myState->pub.mydest == DestRemote ||
		   myState->pub.mydest == DestRemoteExecute);

	myState->portal = portal;
}

static void
printtup_startup(DestReceiver *self, int operation, TupleDesc typeinfo)
{
	DR_printtup *myState = (DR_printtup *) self;
	Portal		portal = myState->portal;

	/*
	 * Create I/O buffer to be used for all messages.  This cannot be inside
	 * tmpcontext, since we want to re-use it across rows.
	 */
	initStringInfo(&myState->buf);

	/*
	 * Create a temporary memory context that we can reset once per row to
	 * recover palloc'd memory.  This avoids any problems with leaks inside
	 * datatype output routines, and should be faster than retail pfree's
	 * anyway.
	 */
	myState->tmpcontext = AllocSetContextCreate(CurrentMemoryContext,
												"printtup",
												ALLOCSET_DEFAULT_SIZES);

	/*
	 * If we are supposed to emit row descriptions, then send the tuple
	 * descriptor of the tuples.
	 */
	if (myState->sendDescrip)
		SendRowDescriptionMessage(&myState->buf,
								  typeinfo,
								  FetchPortalTargetList(portal),
								  portal->formats);

	/* ----------------
	 * We could set up the derived attr info at this time, but we postpone it
	 * until the first call of printtup, for 2 reasons:
	 * 1. We don't waste time (compared to the old way) if there are no
	 *	  tuples at all to output.
	 * 2. Checking in printtup allows us to handle the case that the tuples
	 *	  change type midway through (although this probably can't happen in
	 *	  the current executor).
	 * ----------------
	 */
}

static size_t CHUNK_SIZE = 10000000; // 1 Mb chunks

typedef struct {
    size_t maxsize;
    char *buffer;
    char *copy_buffer;
    char *compression_buffer;
    char **bitmask_pointers;
    char **base_pointers;
    char **data_pointers;
    int **length_pointers;
    bool *data_is_string;
    bool *data_not_null;
    size_t *attribute_lengths;
    size_t transferred_count;
    size_t tuples_per_chunk;
    size_t total_tuples_send;
    size_t total_tuples;
    size_t count;
    void **dict;
    void **dictLength;
    void **context;
    void **contextLength;
    size_t data_sent;
} ResultSetBuffer;

static bool initialized = false;
static ResultSetBuffer rsbuf;

static int USE_COMPRESSION = true;
static int MAX_COMPRESSED_LENGTH = 1000000;

static long beginTime = 0;

//#define PROTOCOL_NULLMASK
#define USE_ZSTD
static int COMPRESSION_LEVEL = -5;

/**
 * Returns the current time in microseconds.
 */
long getMicrotime(){
    struct timeval currentTime;
    gettimeofday(&currentTime, NULL);
    return currentTime.tv_sec * (int)1e6 + currentTime.tv_usec;
}

/*
 * SendRowDescriptionMessage --- send a RowDescription message to the frontend
 *
 * Notes: the TupleDesc has typically been manufactured by ExecTypeFromTL()
 * or some similar function; it does not contain a full set of fields.
 * The targetlist will be NIL when executing a utility function that does
 * not have a plan.  If the targetlist isn't NIL then it is a Query node's
 * targetlist; it is up to us to ignore resjunk columns in it.  The formats[]
 * array pointer might be NULL (if we are doing Describe on a prepared stmt);
 * send zeroes for the format codes in that case.
 */
void
SendRowDescriptionMessage(StringInfo buf, TupleDesc typeinfo,
						  List *targetlist, int16 *formats)
{
	int			natts = typeinfo->natts;
	int			i;
	ListCell   *tlist_item = list_head(targetlist);
    char       *baseptr;
    size_t      rowsize;

    beginTime = getMicrotime();
    ereport(LOG, (errmsg("Setting Begin Time: %ld", beginTime)));

    if (!initialized) {
        rsbuf.maxsize = CHUNK_SIZE;
        rsbuf.buffer = malloc(CHUNK_SIZE);
        rsbuf.copy_buffer = malloc(CHUNK_SIZE);
#ifdef USE_ZSTD
        MAX_COMPRESSED_LENGTH = ZSTD_compressBound(CHUNK_SIZE);
#else
        MAX_COMPRESSED_LENGTH = snappy_max_compressed_length(CHUNK_SIZE);
#endif
        rsbuf.compression_buffer = malloc(MAX_COMPRESSED_LENGTH);
        initialized = true;
        enlargeStringInfo(buf, MAX_COMPRESSED_LENGTH); // TODO: Room for optimization
        // ereport(LOG, (errmsg("Finished Init Phase 1: %ld", getMicrotime() - beginTime)));
    } else {
        free(rsbuf.base_pointers);
        free(rsbuf.data_pointers);
        free(rsbuf.length_pointers);
        free(rsbuf.data_is_string);
        free(rsbuf.attribute_lengths);
        free(rsbuf.data_not_null);
        free(rsbuf.dict);
        free(rsbuf.dictLength);
        free(rsbuf.context);
        free(rsbuf.contextLength);
    }

    rsbuf.transferred_count = 0;
    rsbuf.tuples_per_chunk = 0;
    rsbuf.total_tuples_send = 0;
    rsbuf.total_tuples = 0; // FIXME
    rsbuf.count = 0;
    rsbuf.data_sent = 0;

    rsbuf.base_pointers = malloc(sizeof(char*) * natts);
    rsbuf.data_pointers = malloc(sizeof(char*) * natts);
    rsbuf.length_pointers = malloc(sizeof(int*) * natts);
    rsbuf.data_is_string = malloc(sizeof(bool) * natts);
    rsbuf.attribute_lengths = malloc(sizeof(size_t) * natts);
    rsbuf.data_not_null = malloc(sizeof(bool) * natts);
    rsbuf.dict = malloc(sizeof(void *) * natts);
    rsbuf.dictLength = malloc(sizeof(void *) * natts);
    rsbuf.context = malloc(sizeof(void *) * natts);
    rsbuf.contextLength = malloc(sizeof(void *) * natts);

    rowsize = 0;

    for (i = 0; i < natts; ++i) {
        Form_pg_attribute att = TupleDescAttr(typeinfo, i);
        char category;
        bool preferred;
        ssize_t attribute_length = att->attlen;
        get_type_category_preferred(att->atttypid, &category, &preferred);
        if ((rsbuf.data_is_string[i] = (category == 'S'))) {
            attribute_length = att->atttypmod - 4 + 1; // null terminator
        }
        if (category == 'D') {
            attribute_length = 4; // dates are stored as 4-byte integers
        }
        if (category == 'N' && attribute_length < 0) {
            attribute_length = 64;
        }
        rsbuf.data_not_null[i] = att->attnotnull;
        rsbuf.attribute_lengths[i] = attribute_length;
        rowsize += attribute_length; //attribute length is given in bytes; convert to bits
        Assert(attribute_length > 0); // FIXME: deal with Blobs
    }

    rsbuf.tuples_per_chunk = CHUNK_SIZE / (rowsize + (natts * sizeof (int)));
    baseptr = rsbuf.buffer;

    for (i = 0; i < natts; ++i) {
        Form_pg_attribute att = TupleDescAttr(typeinfo, i);
        rsbuf.base_pointers[i] = baseptr;
        rsbuf.length_pointers[i] = rsbuf.base_pointers[i];
        rsbuf.data_pointers[i] = rsbuf.base_pointers[i] + (rsbuf.tuples_per_chunk * sizeof(int));
        baseptr += (rsbuf.tuples_per_chunk * (rsbuf.attribute_lengths[i] + sizeof (int)))/* + sizeof(int)*/;
        rsbuf.dict[i] = NULL;
        rsbuf.dictLength[i] = NULL;
        rsbuf.context[i] = NULL;
        rsbuf.contextLength[i] = NULL;
    }

    Assert(baseptr - rsbuf.buffer < CHUNK_SIZE);
    Assert(rsbuf.tuples_per_chunk > 0);

	/* tuple descriptor message type */
	pq_beginmessage_reuse(buf, 'T');
	/* # of attrs in tuples */
	pq_sendint16(buf, natts);

    // Compression Information
    pq_sendint16(buf, USE_COMPRESSION);
    pq_sendint32(buf, CHUNK_SIZE);

	/*
	 * Preallocate memory for the entire message to be sent. That allows to
	 * use the significantly faster inline pqformat.h functions and to avoid
	 * reallocations.
	 *
	 * Have to overestimate the size of the column-names, to account for
	 * character set overhead.
	 */
	enlargeStringInfo(buf, (NAMEDATALEN * MAX_CONVERSION_GROWTH /* attname */
							+ sizeof(Oid)	/* resorigtbl */
							+ sizeof(AttrNumber)	/* resorigcol */
							+ sizeof(Oid)	/* atttypid */
							+ sizeof(int16) /* attlen */
							+ sizeof(int32) /* attypmod */
							+ sizeof(int16) /* format */
							) * natts);

	for (i = 0; i < natts; ++i)
	{
		Form_pg_attribute att = TupleDescAttr(typeinfo, i);
		Oid			atttypid = att->atttypid;
		int32		atttypmod = att->atttypmod;
		Oid			resorigtbl;
		AttrNumber	resorigcol;
		int16		format;

		/*
		 * If column is a domain, send the base type and typmod instead.
		 * Lookup before sending any ints, for efficiency.
		 */
		atttypid = getBaseTypeAndTypmod(atttypid, &atttypmod);

		/* Do we have a non-resjunk tlist item? */
		while (tlist_item &&
			   ((TargetEntry *) lfirst(tlist_item))->resjunk)
			tlist_item = lnext(targetlist, tlist_item);
		if (tlist_item)
		{
			TargetEntry *tle = (TargetEntry *) lfirst(tlist_item);

			resorigtbl = tle->resorigtbl;
			resorigcol = tle->resorigcol;
			tlist_item = lnext(targetlist, tlist_item);
		}
		else
		{
			/* No info available, so send zeroes */
			resorigtbl = 0;
			resorigcol = 0;
		}

		if (formats)
			format = formats[i];
		else
			format = 0;

		pq_writestring(buf, NameStr(att->attname));
		pq_writeint32(buf, resorigtbl);
		pq_writeint16(buf, resorigcol);
		pq_writeint32(buf, atttypid);
		pq_writeint16(buf, att->attlen);
		pq_writeint32(buf, atttypmod);
		pq_writeint16(buf, format);
	}

	pq_endmessage_reuse(buf);
}

/*
 * Get the lookup info that printtup() needs
 */
static void
printtup_prepare_info(DR_printtup *myState, TupleDesc typeinfo, int numAttrs)
{
	int16	   *formats = myState->portal->formats;
	int			i;

	/* get rid of any old data */
	if (myState->myinfo)
		pfree(myState->myinfo);
	myState->myinfo = NULL;

	myState->attrinfo = typeinfo;
	myState->nattrs = numAttrs;
	if (numAttrs <= 0)
		return;

	myState->myinfo = (PrinttupAttrInfo *)
		palloc0(numAttrs * sizeof(PrinttupAttrInfo));

	for (i = 0; i < numAttrs; i++)
	{
		PrinttupAttrInfo *thisState = myState->myinfo + i;
		int16		format = (formats ? formats[i] : 0);
		Form_pg_attribute attr = TupleDescAttr(typeinfo, i);

		thisState->format = format;
		if (format == 0)
		{
			getTypeOutputInfo(attr->atttypid,
							  &thisState->typoutput,
							  &thisState->typisvarlena);
			fmgr_info(thisState->typoutput, &thisState->finfo);
		}
		else if (format == 1)
		{
			getTypeBinaryOutputInfo(attr->atttypid,
									&thisState->typsend,
									&thisState->typisvarlena);
			fmgr_info(thisState->typsend, &thisState->finfo);
		}
		else
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("unsupported format code: %d", format)));
	}
}

/* ----------------
 *		printtup --- send a tuple to the client
 * ----------------
 */
static bool
printtup(TupleTableSlot *slot, DestReceiver *self)
{
	TupleDesc	typeinfo = slot->tts_tupleDescriptor;
	DR_printtup *myState = (DR_printtup *) self;
	MemoryContext oldcontext;
	StringInfo	buf = &myState->buf;
	int			natts = typeinfo->natts;
	int			i;

    // ereport(LOG, (errmsg("Printtup")));

	/* Set or update my derived attribute info, if needed */
	if (myState->attrinfo != typeinfo || myState->nattrs != natts)
		printtup_prepare_info(myState, typeinfo, natts);

	/* Make sure the tuple is fully deconstructed */
	slot_getallattrs(slot);

	/* Switch into per-row context so we can recover memory below */
	oldcontext = MemoryContextSwitchTo(myState->tmpcontext);

    rsbuf.count++;

    for (i = 0; i < natts; i++) {
        PrinttupAttrInfo *thisState = myState->myinfo + i;
        Datum		attr = slot->tts_values[i];

        // ereport(LOG, (errmsg("Print Attr: %d", i)));

        if (slot->tts_isnull[i])
        {
            *rsbuf.length_pointers[i] = -1;
            rsbuf.length_pointers[i] += 1;
            continue;
        }

        if (thisState->format == 0)
        {
            char *outputstr;
            outputstr = OutputFunctionCall(&thisState->finfo, attr);
            int len = strlen(outputstr);
            memcpy(rsbuf.data_pointers[i], outputstr, len);
            rsbuf.data_pointers[i] += len;

            *rsbuf.length_pointers[i] = len;
            rsbuf.length_pointers[i] += 1;
        }
        else
        {
            bytea *outputbytes;
            outputbytes = SendFunctionCall(&thisState->finfo, attr);
            int len = VARSIZE(outputbytes) - VARHDRSZ;
            memcpy(rsbuf.data_pointers[i], VARDATA(outputbytes), len);
            rsbuf.data_pointers[i] += len;

            *rsbuf.length_pointers[i] = len;
            rsbuf.length_pointers[i] += 1;
        }
    }

    if (rsbuf.count >= rsbuf.tuples_per_chunk || rsbuf.count % 3000 == 0 //) //1000000 || // always transfer on 1M or 10M total tuples: hacky workaround for not knowing when we reach the end
        || rsbuf.total_tuples_send + rsbuf.count == 10000000 || rsbuf.total_tuples_send + rsbuf.count == 1000000)
    {

        pq_beginmessage_reuse(buf, 'D');

        pq_sendint32(buf, rsbuf.count);


        for (int i = 0; i < natts; ++i) {
            int *length_start = rsbuf.base_pointers[i];
            char *data_start = rsbuf.base_pointers[i] + (rsbuf.tuples_per_chunk * sizeof(int));
            int len = rsbuf.data_pointers[i] - data_start;

            size_t compressed_length_data = MAX_COMPRESSED_LENGTH;
            size_t compressed_length_lengths = MAX_COMPRESSED_LENGTH;

#ifdef USE_ZSTD
            // ereport(LOG, (errmsg("ZSTD Compressing Attribute %d, Uncompressed Length: %d\n", i, len)));


            if (!rsbuf.dict[i]) {
                rsbuf.dict[i] = ZSTD_createCDict(data_start, len, COMPRESSION_LEVEL);
                rsbuf.dictLength[i] = ZSTD_createCDict(length_start, rsbuf.count * sizeof (int), COMPRESSION_LEVEL);
                rsbuf.context[i] = ZSTD_createCCtx();
                rsbuf.contextLength[i] = ZSTD_createCCtx();
                compressed_length_data = ZSTD_compress(rsbuf.compression_buffer, MAX_COMPRESSED_LENGTH, data_start, len, COMPRESSION_LEVEL);
                compressed_length_lengths = ZSTD_compress(rsbuf.compression_buffer + compressed_length_data, MAX_COMPRESSED_LENGTH, length_start, rsbuf.count * sizeof (int), COMPRESSION_LEVEL);
                ereport(LOG, (errmsg("Created dicts: %ld", getMicrotime() - beginTime)));
            } else {
                compressed_length_data = ZSTD_compress_usingCDict(rsbuf.context[i], rsbuf.compression_buffer, MAX_COMPRESSED_LENGTH, data_start, len, rsbuf.dict[i]);
                compressed_length_lengths = ZSTD_compress_usingCDict(rsbuf.contextLength[i], rsbuf.compression_buffer + compressed_length_data, MAX_COMPRESSED_LENGTH, length_start, rsbuf.count * sizeof (int), rsbuf.dictLength[i]);
            }
#else
            // ereport(LOG, (errmsg("Snappy Compressing Attribute %d, Uncompressed Length: %d\n", i, len)));

            ereport(LOG, (errmsg("Snappy blub")));

            if (snappy_compress(data_start, len, rsbuf.compression_buffer, &compressed_length_data) != SNAPPY_OK) {
                // Error
                ereport(LOG, (errmsg("Failed to snappy compress data: %d", i)));
            }

            // ereport(LOG, (errmsg("Snappy Compressing Attribute %d, Compressed Length: %d\n", i, compressed_length_data)));

            if (snappy_compress(length_start, rsbuf.count * sizeof (int), rsbuf.compression_buffer + compressed_length_data, &compressed_length_lengths) != SNAPPY_OK) {
                // Error
                ereport(LOG, (errmsg("Failed to snappy compress length: %d", i)));
            }
#endif

            pq_sendint32(buf, len);
            pq_sendint32(buf, compressed_length_data);
            pq_sendint32(buf, compressed_length_lengths);
            pq_sendbytes(buf, rsbuf.compression_buffer, compressed_length_data + compressed_length_lengths);
        }

        for (i = 0; i < natts; ++i) {
            rsbuf.length_pointers[i] = rsbuf.base_pointers[i]/* + sizeof(int)*/;
            rsbuf.data_pointers[i] = rsbuf.base_pointers[i] + (rsbuf.tuples_per_chunk * sizeof(int));
        }

        rsbuf.total_tuples_send += rsbuf.count;

        rsbuf.count = 0;

        pq_endmessage_reuse(buf);
    }

    MemoryContextSwitchTo(oldcontext);
    MemoryContextReset(myState->tmpcontext);

    return true;
}

/* ----------------
 *		printtup_shutdown
 * ----------------
 */
static void
printtup_shutdown(DestReceiver *self)
{
	DR_printtup *myState = (DR_printtup *) self;

	if (myState->myinfo)
		pfree(myState->myinfo);
	myState->myinfo = NULL;

	myState->attrinfo = NULL;

	if (myState->buf.data)
		pfree(myState->buf.data);
	myState->buf.data = NULL;

	if (myState->tmpcontext)
		MemoryContextDelete(myState->tmpcontext);
	myState->tmpcontext = NULL;
}

/* ----------------
 *		printtup_destroy
 * ----------------
 */
static void
printtup_destroy(DestReceiver *self)
{
	pfree(self);
}

/* ----------------
 *		printatt
 * ----------------
 */
static void
printatt(unsigned attributeId,
		 Form_pg_attribute attributeP,
		 char *value)
{
	printf("\t%2d: %s%s%s%s\t(typeid = %u, len = %d, typmod = %d, byval = %c)\n",
		   attributeId,
		   NameStr(attributeP->attname),
		   value != NULL ? " = \"" : "",
		   value != NULL ? value : "",
		   value != NULL ? "\"" : "",
		   (unsigned int) (attributeP->atttypid),
		   attributeP->attlen,
		   attributeP->atttypmod,
		   attributeP->attbyval ? 't' : 'f');
}

/* ----------------
 *		debugStartup - prepare to print tuples for an interactive backend
 * ----------------
 */
void
debugStartup(DestReceiver *self, int operation, TupleDesc typeinfo)
{
	int			natts = typeinfo->natts;
	int			i;

	/*
	 * show the return type of the tuples
	 */
	for (i = 0; i < natts; ++i)
		printatt((unsigned) i + 1, TupleDescAttr(typeinfo, i), NULL);
	printf("\t----\n");
}

/* ----------------
 *		debugtup - print one tuple for an interactive backend
 * ----------------
 */
bool
debugtup(TupleTableSlot *slot, DestReceiver *self)
{
	TupleDesc	typeinfo = slot->tts_tupleDescriptor;
	int			natts = typeinfo->natts;
	int			i;
	Datum		attr;
	char	   *value;
	bool		isnull;
	Oid			typoutput;
	bool		typisvarlena;

	for (i = 0; i < natts; ++i)
	{
		attr = slot_getattr(slot, i + 1, &isnull);
		if (isnull)
			continue;
		getTypeOutputInfo(TupleDescAttr(typeinfo, i)->atttypid,
						  &typoutput, &typisvarlena);

		value = OidOutputFunctionCall(typoutput, attr);

		printatt((unsigned) i + 1, TupleDescAttr(typeinfo, i), value);
	}
	printf("\t----\n");

	return true;
}

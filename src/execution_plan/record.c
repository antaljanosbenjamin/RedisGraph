/*
* Copyright 2018-2019 Redis Labs Ltd. and Contributors
*
* This file is available under the Apache License, Version 2.0,
* modified with the Commons Clause restriction.
*/

#include "./record.h"
#include "../util/rmalloc.h"
#include <assert.h>

#define RECORD_HEADER(r) (r-1)
#define RECORD_HEADER_ENTRY(r) *(RECORD_HEADER((r)))

Record Record_New(int entries) {
    Record r = rm_calloc((entries + 1), sizeof(Entry));

    // First entry holds records length.
    r[0].type = REC_TYPE_HEADER;
    r[0].value.s = SI_UintVal(entries);

    // Skip header entry.
    return r+1;
}

unsigned int Record_length(const Record r) {
    Entry header = RECORD_HEADER_ENTRY(r);
    int recordLength = header.value.s.uintval;
    return recordLength;
}

Record Record_Clone(const Record r) {
    int recordLength = Record_length(r);
    Record clone = Record_New(recordLength);
    memcpy(clone, r, sizeof(Entry) * recordLength);
    return clone;
}

void Record_Merge(Record a, const Record b) {
    int aLength = Record_length(a);
    int bLength = Record_length(b);
    assert(aLength == bLength);

    for(int i = 0; i < bLength; i++) {
        if(b[i].type != REC_TYPE_UNKNOWN) {
            a[i] = b[i];
        }
    }
}

RecordEntryType Record_GetType(const Record r, int idx) {
    return r[idx].type;
}

SIValue Record_GetEntry(Record r, int idx) {
    RecordEntryType t = Record_GetType(r, idx);
    switch(t) {
        /* TODO Implement a safer mechanism for returning nodes and
         * edges. The pointers returned here access the Record
         * itself, making them unsafe for use past the (frequently
         * short) lifetime of the Record! */
        case REC_TYPE_NODE:
            return SI_NodeVal(&r[idx].value.n);
        case REC_TYPE_EDGE:
            return SI_EdgeVal(&r[idx].value.e);
        case REC_TYPE_SCALAR:
            return r[idx].value.s;
        default:
            assert(false);
    }
}

SIValue Record_GetScalar(Record r,  int idx) {
    r[idx].type = REC_TYPE_SCALAR;
    return r[idx].value.s;
}

Node *Record_GetNode(const Record r,  int idx) {
    r[idx].type = REC_TYPE_NODE;
    return &(r[idx].value.n);
}

Edge *Record_GetEdge(const Record r,  int idx) {
    r[idx].type = REC_TYPE_EDGE;
    return &(r[idx].value.e);
}

GraphEntity *Record_GetGraphEntity(const Record r, int idx) {
    Entry e = r[idx];
    switch(e.type) {
        case REC_TYPE_NODE:
            return (GraphEntity*)Record_GetNode(r, idx);
        case REC_TYPE_EDGE:
            return (GraphEntity*)Record_GetEdge(r, idx);
        case REC_TYPE_SCALAR:
            return (GraphEntity*)(Record_GetScalar(r, idx).ptrval);
        default:
            assert(false);
    }
    return NULL;
}

void Record_AddEntry(Record r, int idx, SIValue v) {
    switch(SI_TYPE(v)) {
      case T_NODE:
          r[idx].value.n = *(Node*)v.ptrval;
          r[idx].type = REC_TYPE_NODE;
          return;
      case T_EDGE:
          r[idx].value.e = *(Edge*)v.ptrval;
          r[idx].type = REC_TYPE_EDGE;
          return;
      default:
          r[idx].value.s = v;
          r[idx].type = REC_TYPE_SCALAR;
  }
}

void Record_AddScalar(Record r, int idx, SIValue v) {
    r[idx].value.s = v;
    r[idx].type = REC_TYPE_SCALAR;
}

void Record_AddNode(Record r, int idx, Node node) {
    r[idx].value.n = node;
    r[idx].type = REC_TYPE_NODE;
}

void Record_AddEdge(Record r, int idx, Edge edge) {
    r[idx].value.e = edge;
    r[idx].type = REC_TYPE_EDGE;
}

size_t Record_ToString(const Record r, char **buf, size_t *buf_cap) {
    uint rLen = Record_length(r);
    SIValue values[rLen];
    for(int i = 0; i < rLen; i++) values[i] = Record_GetEntry(r, i);

    size_t required_len = SIValue_StringConcatLen(values, rLen);

    if(*buf_cap < required_len) {
        *buf = rm_realloc(*buf, sizeof(char) * required_len);
        *buf_cap = required_len;
    }

    return SIValue_StringConcat(values, rLen, *buf, *buf_cap);
}

void Record_Free(Record r) {
    int length = Record_length(r);
    for(int i = 0; i < length; i++) {
        if(r[i].type == REC_TYPE_SCALAR) {
            SIValue_Free(&r[i].value.s);
        }
    }
    rm_free((r-1));
}

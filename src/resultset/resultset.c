/*
* Copyright 2018-2019 Redis Labs Ltd. and Contributors
*
* This file is available under the Apache License, Version 2.0,
* modified with the Commons Clause restriction.
*/

#include "resultset.h"
#include "../value.h"
#include "../util/arr.h"
#include "../util/rmalloc.h"
#include "../query_executor.h"
#include "../grouping/group_cache.h"
#include "../arithmetic/aggregate.h"

/* Checks if we've already seen given records
 * Returns 1 if the string did not exist otherwise 0. */
static int _encounteredRecord(ResultSet *set, const Record r) {
    char *str = NULL;
    size_t len = 0;
    len = Record_ToString(r, &str, &len);

    // Returns 1 if the string did NOT exist otherwise 0
    int newRecord = TrieMap_Add(set->trie, str, len, NULL, NULL);
    rm_free(str);
    return !newRecord;
}

static void _ResultSet_ReplayHeader(const ResultSet *set, const ResultSetHeader *header) {    
    RedisModule_ReplyWithArray(set->ctx, header->columns_len);
    for(int i = 0; i < header->columns_len; i++) {
        Column *c = header->columns[i];
        if(c->alias) {
            RedisModule_ReplyWithStringBuffer(set->ctx, c->alias, strlen(c->alias));
        } else {
            RedisModule_ReplyWithStringBuffer(set->ctx, c->name, strlen(c->name));
        }
    }
}

static void _emit_val(RedisModuleCtx *ctx, const SIValue *v) {
  switch (v->type) {
    case T_STRING:
    case T_CONSTSTRING: // TODO probably impossible for props
      RedisModule_ReplyWithStringBuffer(ctx, v->stringval, strlen(v->stringval));
      return;
    case T_DOUBLE:
      RedisModule_ReplyWithDouble(ctx, v->doubleval);
      return;
  case T_INT32:
      RedisModule_ReplyWithLongLong(ctx, v->intval);
      return;
  case T_BOOL:
      (v->boolval) ? RedisModule_ReplyWithStringBuffer(ctx, "true", 4) : RedisModule_ReplyWithStringBuffer(ctx, "false", 5); // TODO make this pretty
      return;
  case T_NULL:
      RedisModule_ReplyWithNull(ctx);
      return;
  default:
      assert("unhandled type" && false);
  }
}

static void _enumerate_properties(RedisModuleCtx *ctx, const Entity *e) {
    RedisModule_ReplyWithArray(ctx, e->prop_count);
    for (int i = 0; i < e->prop_count; i ++) {
        RedisModule_ReplyWithArray(ctx, 2);
        EntityProperty *prop = &e->properties[i];
        RedisModule_ReplyWithStringBuffer(ctx, prop->name, strlen(prop->name));
        _emit_val(ctx, &prop->value);
    }

}

static void _ReplyWithNode(RedisModuleCtx *ctx, Node *n) {
    // 4 top-level entities in node reply
    RedisModule_ReplyWithArray(ctx, 4);

    // ["type", "node"]
    RedisModule_ReplyWithArray(ctx, 2);
    RedisModule_ReplyWithStringBuffer(ctx, "type", 4);
    RedisModule_ReplyWithStringBuffer(ctx, "node", 4);

    // ["id", id(int)]
    RedisModule_ReplyWithArray(ctx, 2);
    RedisModule_ReplyWithStringBuffer(ctx, "id", 2);
    RedisModule_ReplyWithLongLong(ctx, n->entity->id);

    // ["labels", [label(str)]]
    RedisModule_ReplyWithArray(ctx, 2);
    RedisModule_ReplyWithStringBuffer(ctx, "labels", 6);
    RedisModule_ReplyWithArray(ctx, 1);
    // Retrieve label
    /*
    TODO don't know how to actually do this, since NodeID is not accessible here.
    consider updating node/edge structs to contain their IDs?
    alternately, we have ID at time of scan op...
    */
    // RedisModule_ReplyWithStringBuffer(ctx, n->label, strlen(n->label));
    GraphContext *gc = GraphContext_GetFromLTS();
    int labelID = Graph_GetNodeLabel(gc->g, ENTITY_GET_ID(n));
    const char *label = gc->node_stores[labelID]->label;
    RedisModule_ReplyWithStringBuffer(ctx, label, strlen(label));

    // [properties, [properties]]
    RedisModule_ReplyWithArray(ctx, 2);
    RedisModule_ReplyWithStringBuffer(ctx, "properties", 10);
    _enumerate_properties(ctx, n->entity);
}

static void _ReplyWithEdge(RedisModuleCtx *ctx, Edge *e) {
    // 6 top-level entities in node reply
    RedisModule_ReplyWithArray(ctx, 6);

    // ["type", "relation"]
    RedisModule_ReplyWithArray(ctx, 2);
    RedisModule_ReplyWithStringBuffer(ctx, "type", 4);
    RedisModule_ReplyWithStringBuffer(ctx, "relation", 8);

    // ["id", id(int)]
    RedisModule_ReplyWithArray(ctx, 2);
    RedisModule_ReplyWithStringBuffer(ctx, "id", 2);
    RedisModule_ReplyWithLongLong(ctx, e->entity->id);

    RedisModule_ReplyWithArray(ctx, 2);
    RedisModule_ReplyWithStringBuffer(ctx, "relation_type", 13);
    GraphContext *gc = GraphContext_GetFromLTS();
    // TODO validate this call
    int idx = Graph_GetEdgeRelation(gc->g, e);
    const char *label = gc->relation_stores[idx]->label;
    RedisModule_ReplyWithStringBuffer(ctx, label, strlen(label));

    // src
    RedisModule_ReplyWithArray(ctx, 2);
    RedisModule_ReplyWithStringBuffer(ctx, "src_node", 8);
    RedisModule_ReplyWithLongLong(ctx, e->srcNodeID);

    // dest
    RedisModule_ReplyWithArray(ctx, 2);
    RedisModule_ReplyWithStringBuffer(ctx, "dest_node", 9);
    RedisModule_ReplyWithLongLong(ctx, e->destNodeID);

    // [properties, [properties]]
    RedisModule_ReplyWithArray(ctx, 2);
    RedisModule_ReplyWithStringBuffer(ctx, "properties", 10);
    _enumerate_properties(ctx, e->entity);

}

static void _ResultSet_ReplayRecord(ResultSet *s, const Record r) {
    // Skip record.
    if(s->skipped < s->skip) {
        s->skipped++;
        return;
    }

    char value[2048] = {0};
    uint column_count = s->header->columns_len;
    RedisModule_ReplyWithArray(s->ctx, column_count);

    int written;
    for(int i = 0; i < column_count; i++) {
        // can replace Record_GetScalar with something else,
        // then add handling to unpack entities. Would that have a performance impact, though?
        // Alternately, header can track type stored in each column.
        RecordEntryType t = Record_GetType(r, i);
        switch (t) {
            case REC_TYPE_NODE:
                _ReplyWithNode(s->ctx, Record_GetNode(r, i));
                break;
            case REC_TYPE_EDGE:
                _ReplyWithEdge(s->ctx, Record_GetEdge(r, i));
                break;
                   // TODO
                break;
            case REC_TYPE_SCALAR:
                written = SIValue_ToString(Record_GetScalar(r, i), value, 2048);
                RedisModule_ReplyWithStringBuffer(s->ctx, value, written);
                break;
            default:
                assert("unhandled record type?" && false);

        }
    }
}

// Prepare replay.
static void _ResultSet_SetupReply(ResultSet *set) {
    // resultset + statistics, in that order.
    RedisModule_ReplyWithArray(set->ctx, 2);

    // We don't know at this point the number of records, we're about to return.
    RedisModule_ReplyWithArray(set->ctx, REDISMODULE_POSTPONED_ARRAY_LEN);
}

static void _ResultSet_ReplayStats(RedisModuleCtx* ctx, ResultSet* set) {
    char buff[512] = {0};
    size_t resultset_size = 1; /* query execution time. */
    int buflen;

    if(set->stats.labels_added > 0) resultset_size++;
    if(set->stats.nodes_created > 0) resultset_size++;
    if(set->stats.properties_set > 0) resultset_size++;
    if(set->stats.relationships_created > 0) resultset_size++;
    if(set->stats.nodes_deleted > 0) resultset_size++;
    if(set->stats.relationships_deleted > 0) resultset_size++;

    RedisModule_ReplyWithArray(ctx, resultset_size);

    if(set->stats.labels_added > 0) {
        buflen = sprintf(buff, "Labels added: %d", set->stats.labels_added);
        RedisModule_ReplyWithStringBuffer(ctx, (const char*)buff, buflen);
    }

    if(set->stats.nodes_created > 0) {
        buflen = sprintf(buff, "Nodes created: %d", set->stats.nodes_created);
        RedisModule_ReplyWithStringBuffer(ctx, (const char*)buff, buflen);
    }

    if(set->stats.properties_set > 0) {
        buflen = sprintf(buff, "Properties set: %d", set->stats.properties_set);
        RedisModule_ReplyWithStringBuffer(ctx, (const char*)buff, buflen);
    }

    if(set->stats.relationships_created > 0) {
        buflen = sprintf(buff, "Relationships created: %d", set->stats.relationships_created);
        RedisModule_ReplyWithStringBuffer(ctx, (const char*)buff, buflen);
    }

    if(set->stats.nodes_deleted > 0) {
        buflen = sprintf(buff, "Nodes deleted: %d", set->stats.nodes_deleted);
        RedisModule_ReplyWithStringBuffer(ctx, (const char*)buff, buflen);
    }

    if(set->stats.relationships_deleted > 0) {
        buflen = sprintf(buff, "Relationships deleted: %d", set->stats.relationships_deleted);
        RedisModule_ReplyWithStringBuffer(ctx, (const char*)buff, buflen);
    }
}

static Column* _NewColumn(char *name, char *alias) {
    Column* column = rm_malloc(sizeof(Column));
    column->name = name;
    column->alias = alias;
    return column;
}

void static _Column_Free(Column* column) {
    /* No need to free alias,
     * it will be freed as part of AST_Free. */
    rm_free(column->name);
    rm_free(column);
}

void ResultSet_CreateHeader(ResultSet *resultset) {
    assert(resultset->header == NULL && resultset->recordCount == 0);

    const AST *ast = AST_GetFromLTS();
    ResultSetHeader* header = rm_malloc(sizeof(ResultSetHeader));
    header->columns_len = 0;
    header->columns = NULL;

    if(ast->returnNode != NULL) {
        header->columns_len = array_len(ast->returnNode->returnElements);
        header->columns = rm_malloc(sizeof(Column*) * header->columns_len);
    }

    for(int i = 0; i < header->columns_len; i++) {
        AST_ReturnElementNode* returnElementNode = ast->returnNode->returnElements[i];

        AR_ExpNode* ar_exp = AR_EXP_BuildFromAST(ast, returnElementNode->exp);

        char* column_name;
        AR_EXP_ToString(ar_exp, &column_name);
        Column* column = _NewColumn(column_name, returnElementNode->alias);
        AR_EXP_Free(ar_exp);

        header->columns[i] = column;
    }

    resultset->header = header;
    /* Replay with table header. */
    _ResultSet_ReplayHeader(resultset, header);
}

static void _ResultSetHeader_Free(ResultSetHeader* header) {
    if(!header) return;

    for(int i = 0; i < header->columns_len; i++) _Column_Free(header->columns[i]);

    if(header->columns != NULL) {
        rm_free(header->columns);
    }

    rm_free(header);
}

// Checks to see if resultset can acecpt additional records.
bool ResultSet_Full(const ResultSet* set) {
    return (set->limit != RESULTSET_UNLIMITED && set->recordCount >= set->limit);
}

bool ResultSet_Limited(const ResultSet* set) {
    return (set && set->limit != RESULTSET_UNLIMITED);
}

ResultSet* NewResultSet(AST* ast, RedisModuleCtx *ctx) {
    ResultSet* set = (ResultSet*)malloc(sizeof(ResultSet));
    set->ctx = ctx;
    set->trie = NULL;
    set->limit = RESULTSET_UNLIMITED;
    set->skip = (ast->skipNode) ? ast->skipNode->skip : 0;
    set->skipped = 0;
    set->distinct = (ast->returnNode && ast->returnNode->distinct);
    set->recordCount = 0;    
    set->header = NULL;
    set->bufferLen = 2048;
    set->buffer = malloc(set->bufferLen);

    set->stats.labels_added = 0;
    set->stats.nodes_created = 0;
    set->stats.properties_set = 0;
    set->stats.relationships_created = 0;
    set->stats.nodes_deleted = 0;
    set->stats.relationships_deleted = 0;

    // Account for skipped records.
    if(ast->limitNode != NULL) set->limit = set->skip + ast->limitNode->limit;
    if(set->distinct) set->trie = NewTrieMap();

    _ResultSet_SetupReply(set);

    return set;
}

int ResultSet_AddRecord(ResultSet* set, Record r) {
    if(ResultSet_Full(set)) return RESULTSET_FULL;
    
    /* TODO: Incase of an aggregated query, there's no need to distinct check
     * groups are already distinct by key.
     * TODO: indicate we've skipped record. */
    if(set->distinct && _encounteredRecord(set, r)) return RESULTSET_OK;

    set->recordCount++;
    _ResultSet_ReplayRecord(set, r);
    return RESULTSET_OK;
}

void ResultSet_Replay(ResultSet* set) {
    // Ensure that we're returning a valid number of records.
    size_t resultset_size = 0;
    if (set->skip < set->recordCount) {
      resultset_size = set->recordCount - set->skip;
    }

    if(set->header) resultset_size++;

    RedisModule_ReplySetArrayLength(set->ctx, resultset_size);
    _ResultSet_ReplayStats(set->ctx, set);
}

void ResultSet_Free(ResultSet *set) {
    if(!set) return;

    free(set->buffer);
    if(set->header) _ResultSetHeader_Free(set->header);
    if(set->trie != NULL) TrieMap_Free(set->trie, TrieMap_NOP_CB);
    free(set);
}

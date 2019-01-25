/*
* Copyright 2018-2019 Redis Labs Ltd. and Contributors
*
* This file is available under the Apache License, Version 2.0,
* modified with the Commons Clause restriction.
*/

#include <assert.h>
#include "query_executor.h"
#include "graph/graph.h"
#include "graph/entities/node.h"
#include "stores/store.h"
#include "util/arr.h"
#include "util/vector.h"
#include "parser/grammar.h"
#include "arithmetic/agg_ctx.h"
#include "arithmetic/repository.h"
#include "parser/parser_common.h"

static void _inlineProperties(AST *ast) {
    /* Migrate inline filters to WHERE clause. */
    if(!ast->matchNode) return;
    // Vector *entities = ast->matchNode->graphEntities;
    Vector *entities = ast->matchNode->_mergedPatterns;

    char *alias;
    char *property;
    AST_ArithmeticExpressionNode *lhs;
    AST_ArithmeticExpressionNode *rhs;

    /* Foreach entity. */
    for(int i = 0; i < Vector_Size(entities); i++) {
        AST_GraphEntity *entity;
        Vector_Get(entities, i, &entity);

        alias = entity->alias;

        Vector *properties = entity->properties;
        if(properties == NULL) {
            continue;
        }

        /* Foreach property. */
        for(int j = 0; j < Vector_Size(properties); j+=2) {
            SIValue *key;
            SIValue *val;

            // Build the left-hand filter value from the node alias and property
            Vector_Get(properties, j, &key);
            property = key->stringval;
            lhs = New_AST_AR_EXP_VariableOperandNode(alias, property);

            // Build the right-hand filter value from the specified constant
            // TODO can update grammar so that this constant is already an ExpressionNode
            // instead of an SIValue
            Vector_Get(properties, j+1, &val);
            rhs = New_AST_AR_EXP_ConstOperandNode(*val);

            AST_FilterNode *filterNode = New_AST_PredicateNode(lhs, EQ, rhs);
            
            /* Create WHERE clause if missing. */
            if(ast->whereNode == NULL) {
                ast->whereNode = New_AST_WhereNode(filterNode);
            } else {
                /* Introduce filter with AND operation. */
                AST_FilterNode *left = ast->whereNode->filters;
                AST_FilterNode *right = filterNode;
                ast->whereNode->filters = New_AST_ConditionNode(left, AND, right);
            }
        }
    }
}

/* Shares merge pattern with match clause. */
static void _replicateMergeClauseToMatchClause(AST *ast) {    
    assert(ast->mergeNode && !ast->matchNode);

    /* Match node is expecting a vector of vectors,
     * and so we have to wrap merge graph entities vector
     * within another vector
     * wrappedEntities will be freed by match clause. */
    Vector *wrappedEntities = NewVector(Vector*, 1);
    Vector_Push(wrappedEntities, ast->mergeNode->graphEntities);
    ast->matchNode = New_AST_MatchNode(wrappedEntities);
}

void ExpandCollapsedNodes(AST *ast) {    
    char buffer[256];
    GraphContext *gc = GraphContext_GetFromLTS();
    
    /* Expanding the RETURN clause is a two phase operation:
     * 1. Scan through every arithmetic expression within the original
     * RETURN clause and add it to a temporary vector,
     * if we bump into an asterisks marker indicating we should expand
     * all nodes, relations and paths, add thoese to the temporary vector.
     * 
     * 2. Scanning though the temporary vector we expand each collapsed entity
     * this will form the final RETURN clause. */

    AST_ReturnNode *returnClause = ast->returnNode;
    size_t returnElementCount = array_len(returnClause->returnElements);
    AST_ReturnElementNode **elementsToExpand = array_new(AST_ReturnElementNode*, returnElementCount);

    TrieMap *identifiers = NewTrieMap();
    MatchClause_DefinedEntities(ast->matchNode, identifiers);
    CreateClause_DefinedEntities(ast->createNode, identifiers);

    // Scan through return elements, see if we can find '*' marker.
    for(int i = 0; i < returnElementCount; i++) {
        AST_ReturnElementNode *retElement = returnClause->returnElements[i];        
        if(retElement->asterisks) {
            // TODO: '*' can not be mixed with any other expression!
            // TODO would be better to handle this as AST validation
            array_clear(elementsToExpand);
            /* Expand with "RETURN *" queries.
             * Extract all entities from MATCH clause and add them to RETURN clause.
             * These will get expended later on. */
            char *ptr;
            tm_len_t len;
            void *value;
            TrieMapIterator *it = TrieMap_Iterate(identifiers, "", 0);
            while(TrieMapIterator_Next(it, &ptr, &len, &value)) {
                AST_GraphEntity *entity = (AST_GraphEntity*)value;
                if(entity->anonymous) continue;

                len = MIN(255, len);
                memcpy(buffer, ptr, len);
                buffer[len] = '\0';

                AST_ArithmeticExpressionNode *arNode = New_AST_AR_EXP_VariableOperandNode(buffer, NULL);
                AST_ReturnElementNode *returnEntity = New_AST_ReturnElementNode(arNode, NULL);
                elementsToExpand = array_append(elementsToExpand, returnEntity);
            }

            TrieMapIterator_Free(it);            
            Free_AST_ReturnElementNode(retElement);
            break;
        } else {
            elementsToExpand = array_append(elementsToExpand, retElement);
        }
    }

    /* Override previous return clause. */
    TrieMap_Free(identifiers, TrieMap_NOP_CB);
    array_free(returnClause->returnElements);
    returnClause->returnElements = elementsToExpand;
}

AST* ParseQuery(const char *query, size_t qLen, char **errMsg) {
    return Query_Parse(query, qLen, errMsg);
}

AST_Validation AST_PerformValidations(RedisModuleCtx *ctx, AST *ast) {
    char *reason;
    if (AST_Validate(ast, &reason) != AST_VALID) {
        RedisModule_ReplyWithError(ctx, reason);
        free(reason);
        return AST_INVALID;
    }
    return AST_VALID;
}

void ModifyAST(GraphContext *gc, AST *ast) {
    if(ast->mergeNode) {
        /* Create match clause which will try to match 
         * against pattern specified within merge clause. */
        _replicateMergeClauseToMatchClause(ast);
    }

    AST_NameAnonymousNodes(ast);
    _inlineProperties(ast);
}

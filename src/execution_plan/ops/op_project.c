/*
* Copyright 2018-2019 Redis Labs Ltd. and Contributors
*
* This file is available under the Apache License, Version 2.0,
* modified with the Commons Clause restriction.
*/

#include "op_project.h"
#include "../../util/arr.h"
#include "../../query_executor.h"

static void _buildExpressions(Project *op) {
    // Compute projected record length:
    // Number of returned expressions + number of order-by expressions.
    ResultSet_CreateHeader(op->resultset);

    const AST *ast = op->ast;
    uint orderByExpCount = 0;
    uint returnExpCount = array_len(ast->returnNode->returnElements);
    if(ast->orderNode) orderByExpCount = array_len(ast->orderNode->expressions);
    uint expressionCount = returnExpCount + orderByExpCount;
    
    op->projectedRecordLen = expressionCount;
    op->expressions = array_new(AR_ExpNode*, expressionCount);

    // Compose RETURN clause expressions.
    for(uint i = 0; i < returnExpCount; i++) {
        AST_ArithmeticExpressionNode *exp = ast->returnNode->returnElements[i]->exp;
        op->expressions = array_append(op->expressions, AR_EXP_BuildFromAST(ast, exp));
    }

    // Compose ORDER BY expressions.
    for(uint i = 0; i < orderByExpCount; i++) {
        AST_ArithmeticExpressionNode *exp = ast->orderNode->expressions[i];
        op->expressions = array_append(op->expressions, AR_EXP_BuildFromAST(ast, exp));
    }
}

OpBase* NewProjectOp(ResultSet *resultset) {
    Project *project = malloc(sizeof(Project));
    project->ast = AST_GetFromLTS();
    project->singleResponse = false;    
    project->expressions = NULL;
    project->resultset = resultset;

    // Set our Op operations
    OpBase_Init(&project->op);
    project->op.name = "Project";
    project->op.type = OPType_PROJECT;
    project->op.consume = ProjectConsume;
    project->op.reset = ProjectReset;
    project->op.free = ProjectFree;

    return (OpBase*)project;
    return NULL;
}

Record ProjectConsume(OpBase *opBase) {
    Project *op = (Project*)opBase;
    Record r = NULL;

    if(op->op.childCount) {
        OpBase *child = op->op.children[0];
        r = child->consume(child);
        if(!r) return NULL;
    } else {
        // QUERY: RETURN 1+2
        // Return a single record followed by NULL
        // on the second call.
        if(op->singleResponse) return NULL;
        op->singleResponse = true;
        r = Record_New(0);  // Fake empty record.
    }

    if(!op->expressions) _buildExpressions(op);

    Record projectedRec = Record_New(op->projectedRecordLen);

    uint expIdx = 0;
    uint expCount = array_len(op->expressions);
    uint returnExpCount = array_len(op->ast->returnNode->returnElements);
    // Evaluate RETURN clause expressions.
    for(; expIdx < returnExpCount; expIdx++) {
        AR_ExpNode *exp = op->expressions[expIdx];
        // Incase expression is aliased, add it to record
        // as it might be referenced by other expressions:
        // e.g. RETURN n.v AS X ORDER BY X * X
        char *alias = op->ast->returnNode->returnElements[expIdx]->alias;
        // Check if expression refers to a full entity
        if (AR_EXP_IS_GRAPH_ENTITY(exp)) {
            int record_offset = exp->operand.variadic.entity_alias_idx;
            RecordEntryType t = Record_GetType(r, record_offset);

            // Copy the entity to the projected record with the appropriate type
            if (t == REC_TYPE_NODE) {
                Node *n = Record_GetNode(r, record_offset);
                Record_AddNode(projectedRec, expIdx, *n);
                if(alias) Record_AddNode(r, AST_GetAliasID(op->ast, alias), *n);
            } else if (t == REC_TYPE_EDGE) {
                Edge *e = Record_GetEdge(r, record_offset);
                Record_AddEdge(projectedRec, expIdx, *e);
                if(alias) Record_AddEdge(r, AST_GetAliasID(op->ast, alias), *e);
            } else {
                assert("Encountered unhandled type" && false);
            }
        } else {
            // Add a scalar to the projected record
            SIValue v = AR_EXP_Evaluate(exp, r);
            Record_AddScalar(projectedRec, expIdx, v);
            if(alias) Record_AddScalar(r, AST_GetAliasID(op->ast, alias), v);
        }

    }

    // Evaluate ORDER BY clause expressions.
    for(; expIdx < expCount; expIdx++) {
        SIValue v = AR_EXP_Evaluate(op->expressions[expIdx], r);
        Record_AddScalar(projectedRec, expIdx, v);
    }

    Record_Free(r);
    return projectedRec;
}

OpResult ProjectReset(OpBase *ctx) {
    return OP_OK;
}

void ProjectFree(OpBase *opBase) {
    Project *op = (Project*)opBase;
    if(op->expressions) {
        uint expCount = array_len(op->expressions);
        for(uint i = 0; i < expCount; i++) AR_EXP_Free(op->expressions[i]);
        array_free(op->expressions);
    }
}

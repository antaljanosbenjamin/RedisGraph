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

    NEWAST *ast = op->ast;

    op->orderByExpCount = ast->order_expression_count;
    op->returnExpCount = array_len(ast->return_expressions);
    
    op->expressions = rm_malloc((op->orderByExpCount + op->returnExpCount) * sizeof(AR_ExpNode*));

    // TODO redundancy; already performed by ResultSet header creation
    // Compose RETURN clause expressions.
    for(uint i = 0; i < op->returnExpCount; i++) {
        // TODO weird?
        op->expressions[i] = ast->return_expressions[i]->exp;
    }

    // Compose ORDER BY expressions.
    for(uint i = 0; i < op->orderByExpCount; i++) {
        op->expressions[i + op->returnExpCount] = ast->order_expressions[i];
    }
}

OpBase* NewProjectOp(ResultSet *resultset) {
    Project *project = malloc(sizeof(Project));
    project->ast = NEWAST_GetFromLTS();
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

    Record projectedRec = Record_New(op->returnExpCount + op->orderByExpCount);

    uint expIdx = 0;
    // Evaluate RETURN clause expressions.
    for(; expIdx < op->returnExpCount; expIdx++) {
        SIValue v = AR_EXP_Evaluate(op->expressions[expIdx], r);
        Record_AddScalar(projectedRec, expIdx, v);

        // Incase expression is aliased, add it to record
        // as it might be referenced by other expressions:
        // e.g. RETURN n.v AS X ORDER BY X * X
        // TODO aliases
        // const char *alias = op->ast->return_expressions[expIdx]->alias;
        // if(alias) Record_AddScalar(r, NEWAST_GetAliasID(op->ast, (char*)alias), v);
    }

    // Evaluate ORDER BY clause expressions.
    for(; expIdx < op->returnExpCount + op->orderByExpCount; expIdx++) {
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
        uint expCount = op->returnExpCount + op->orderByExpCount;
        for(uint i = 0; i < expCount; i++) AR_EXP_Free(op->expressions[i]);
        rm_free(op->expressions);
    }
}

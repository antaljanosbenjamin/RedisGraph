//------------------------------------------------------------------------------
// GB_SelectOp_check: check and print a select operator
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

//------------------------------------------------------------------------------

#include "GB.h"

GrB_Info GB_SelectOp_check  // check a GraphBLAS select operator
(
    const GxB_SelectOp op,  // GraphBLAS operator to print and check
    const char *name,       // name of the operator
    int pr,                 // 0: print nothing, 1: print header and errors,
                            // 2: print brief, 3: print all
    FILE *f,                // file for output
    GB_Context Context
)
{ 

    //--------------------------------------------------------------------------
    // check inputs
    //--------------------------------------------------------------------------

    if (pr > 0) GBPR ("\nGraphBLAS SelectOp: %s: ", GB_NAME) ;

    if (op == NULL)
    { 
        // GrB_error status not modified since this may be an optional argument
        if (pr > 0) GBPR ("NULL\n") ;
        return (GrB_NULL_POINTER) ;
    }

    //--------------------------------------------------------------------------
    // check object
    //--------------------------------------------------------------------------

    GB_CHECK_MAGIC (op, "SelectOp") ;

    if (pr > 0 && op->opcode >= GB_USER_SELECT_C_opcode)
    { 
        GBPR ("user-defined: ") ;
    }

    if (pr > 0) GBPR ("C=%s(A,k)\n", op->name) ;

    if (op->function == NULL && op->opcode >= GB_USER_SELECT_C_opcode)
    { 
        if (pr > 0) GBPR ("function pointer is NULL\n") ;
        return (GB_ERROR (GrB_INVALID_OBJECT, (GB_LOG,
            "SelectOp has a NULL function pointer: %s [%s]",
            GB_NAME, op->name))) ;
    }

    if (!(op->opcode == GB_TRIL_opcode ||
          op->opcode == GB_TRIU_opcode ||
          op->opcode == GB_DIAG_opcode ||
          op->opcode == GB_OFFDIAG_opcode ||
          op->opcode == GB_NONZERO_opcode ||
          op->opcode == GB_USER_SELECT_C_opcode ||
          op->opcode == GB_USER_SELECT_R_opcode))
    { 
        if (pr > 0) GBPR ("invalid opcode\n") ;
        return (GB_ERROR (GrB_INVALID_OBJECT, (GB_LOG,
            "SelectOp has an invalid opcode: %s [%s]", GB_NAME, op->name))) ;
    }

    if (op->xtype != NULL)
    { 
        GrB_Info info = GB_Type_check (op->xtype, "xtype", pr, f, Context) ;
        if (info != GrB_SUCCESS)
        { 
            if (pr > 0) GBPR ("SelectOP has an invalid xtype\n") ;
            return (GB_ERROR (GrB_INVALID_OBJECT, (GB_LOG,
                "SelectOp has an invalid xtype: %s [%s]", GB_NAME, op->name))) ;
        }
    }

    return (GrB_SUCCESS) ;
}


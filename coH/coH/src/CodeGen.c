/**@file
 * @brief     Code Generator.
 * @author    Igor Lesik
 * @copyright Igor Lesik 2011-2012.
 *
 * License:   Distributed under the Boost Software License, Version 1.0.
 *            (See http://www.boost.org/LICENSE_1_0.txt)
 *
 */
#include "CodeGen.h"

#include <assert.h>

#include "ast.h"
#include "debug.h"
#include "be.h"

#ifdef NDEBUG
    static inline void debug(uint64_t flags, const char* frmt, ...) {}
#else
    #define debug(flags, frmt, ...)\
        debugModule(DBG_CODEGEN | flags, "codegen", frmt, ##__VA_ARGS__)
#endif


void CodeGen_create(CodeGen* self)
{
}

void CodeGen_destroy(CodeGen* self)
{
}

bool
CodeGen_run(CodeGen* self, AST* ast, FILE* fh, FILE* fc)
{

    AST** ast_child = NULL;
    AST_FOR_EACH(ast, ast_child)
    {
        debug(DBG_L_NOISY, "gen token: %d, %s\n", (*ast_child)->token.type, (*ast_child)->token.str.p);

        switch((*ast_child)->token.type)
        {
        case TOKEN_CLASS:
            be_defClass(fh, 0, *ast_child);
            break;
        default:
            PRINT("************* %s", (*ast_child)->token.str.p);
            break;
        }

        CodeGen_run(self, *ast_child, fh, fc);
    }

    return true;
}


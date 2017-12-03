/**@file
 * @brief     AST.
 * @author    Igor Lesik
 * @copyright Igor Lesik 2011-2012.
 *
 * License:   Distributed under the Boost Software License, Version 1.0.
 *            (See http://www.boost.org/LICENSE_1_0.txt)
 *
 */
#include "ast.h"

//#include "file.h"
#include "debug.h"

#ifdef NDEBUG
    static inline void debug(uint64_t flags, const char* frmt, ...) {}
#else
    #define debug(flags, frmt, ...)\
        debugModule(DBG_AST | flags, "ast", frmt, ##__VA_ARGS__)
#endif


#define FOR_EACH(child) \
    for (child = ASTList_begin(&self->children); child < ASTList_end(&self->children); ++child)



void AST_destroy(AST* self)
{
    AST** child = NULL;
    FOR_EACH(child) {
        AST_destroy(*child);
        free(*child);
    }

    ASTList_destroy(&self->children);

    ASToken_destroy(&self->token);
}


const char* ASToken_typeToString(ASTokenType type)
{
    static const char* name[TOKEN__END] = {
        "NIL",
         #define ASTOKEN(name) #name
         #include "astoken.h"
         #undef ASTOKEN
    };

    return name[type];
}


void AST_print(AST* self, FILE* f, int indent)
{
    fprintf(f, "%*s %s> %s\n", indent, "",
        ASToken_typeToString(self->token.type), self->token.str.p);

    AST_printChildren(self, f, indent + 2);
}

void AST_printChildren(AST* self, FILE* f, int indent)
{
    AST** child = NULL;
    FOR_EACH(child) {
        AST_print(*child, f, indent);
    } 
}



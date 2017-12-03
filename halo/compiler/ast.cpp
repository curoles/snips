/**@file
 * AST.
 *
 * Copyright (C) 2011 Igor Lesik.
 * License:   Distributed under the Boost Software License, Version 1.0.
 *            (See http://www.boost.org/LICENSE_1_0.txt)
 *
 */
#include "ast.h"

#include "file.h"
#include "debug.h"

#ifdef NDEBUG
    static inline void debug(uint64_t, const char*, ...) {}
#else
    #define debug(flags, frmt, ...)\
        debugModule(Dbg::AST | flags, "ast", frmt, ##__VA_ARGS__)
#endif


#define FOR_EACH(child) \
    for (AST** child = children.begin(); child < children.end(); ++child) 

AST::
~AST()
{
    FOR_EACH(child) {
        delete *child;
    }
}

/*static*/ const char* AST::Token::typeToString(Type type)
{
    static const char* name[AST::Token::TOKEN__END] = {
        "NIL",
         #define ASTOKEN(name) #name
         #include "astoken.h"
         #undef ASTOKEN
    };

    return name[type];
}

void
AST::
print(File& f, int indent)
{
    fprintf(f, "%*s %s> %s\n", indent, "",
        Token::typeToString(token.type), token.str.c_str());

    printChildren(f, indent + 2);
}

void
AST::
printChildren(File& f, int indent)
{
    FOR_EACH(child) {
        (*child)->print(f, indent);
    } 
}

#if 0
void
AstNodeId::
print(int indent)
{
    PRINT("%*s %s> %s:%s\n", indent, "",
        Token::typeToString(token.type), token.str.c_str(), type.c_str());

    printChildren(indent + 2);
}
#endif

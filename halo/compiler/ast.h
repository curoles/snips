/**@file
 * AST.
 *
 * Copyright (C) 2011 Igor Lesik.
 * License:   Distributed under the Boost Software License, Version 1.0.
 *            (See http://www.boost.org/LICENSE_1_0.txt)
 *
 */
#pragma once
#ifndef HALO_AST_H_INCLUDED
#define HALO_AST_H_INCLUDED

#include "vector.h"
#include "ztring.h"

class File;
class AST;

class ASTList
{
    typedef AST* ElemType;
private:
    vector_t v;

public:
    ASTList() { vector_init(&v, sizeof(ElemType)); }

   ~ASTList() {
        vector_destroy(&v);
    }

    ElemType operator[](size_t index) {
        return vector_at(ElemType, v, index);
    }

    void push_back(ElemType el) {
        vector_push_back(ElemType, v, el);
    }

    ElemType* begin() { return (ElemType*)v.element + 0; }
    ElemType* end()   { return (ElemType*)v.element + v.size; }

    ElemType* front() { return begin(); }
    ElemType* back()  { return end() - 1; }

    inline size_t size() const { return v.size; }
    inline bool empty() const { return (size() == 0); }
};

class AST
{
public:

    struct Token
    {
        enum Type {
            TOKEN__BEGIN = 0,
            TOKEN_NIL = 0, // no root node
            #define ASTOKEN(name) TOKEN_##name
            #include "astoken.h"
            #undef ASTOKEN
            TOKEN__END
        };

        Type type;
        string str;

        Token(Type type, const char* s):type(type), str(s){}

        Type getType() const { return type; }

        static const char* typeToString(Type);
    };

public:

    Token token;

    ASTList children;

public:

    AST(Token::Type token_type, const char* token_str):
        token(token_type, token_str){}

    virtual ~AST();

    inline void addChild(AST* child) {
        children.push_back(child);
    }

    virtual void print(File& f, int indent);
    void printChildren(File& f, int indent);

    friend class Parser;
};

class AstNodeId : public AST
{
public:

    AstNodeId(const char* name):
        AST(Token::TOKEN_ID, name){}

    //void print(int indent);

};

#endif

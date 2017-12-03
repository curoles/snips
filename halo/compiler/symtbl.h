/**@file
 * Symbol Table.
 *
 * Copyright (C) 2011 Igor Lesik.
 * License:   Distributed under the Boost Software License, Version 1.0.
 *            (See http://www.boost.org/LICENSE_1_0.txt)
 *
 */
#pragma once
#ifndef HALO_SYMTBL_H_INCLUDED
#define HALO_SYMTBL_H_INCLUDED

#include "ztring.h"
#include "debug.h"

struct Sym
{
    enum Type {
        SYM   = 0x00010000,
        SCOPE = 0x00020000,
        NAMED = 0x00100000,
        DAGGR = 0x01000000 | NAMED | SCOPE,
        ARGS  = 0x02000000 | NAMED | SCOPE,
        TYPE  = 0x10000000,

        VAL   = 0x0001 | NAMED | SYM | TYPE,
        VAR   = 0x0003 | NAMED | SYM | TYPE,

        PKG   = 0x0010 | NAMED | SCOPE,
        BLOCK = 0x0020 | SCOPE,

        CLASS = 0x0100 | NAMED | SYM | DAGGR,
        OBJ   = 0x0200 | NAMED | SYM | DAGGR,
        FUNC  = 0x0300 | NAMED | SYM | ARGS,
        METHOD= 0x0400 | NAMED | SYM | ARGS,
    };

    inline int isSym()   const { return category | SYM; }
    inline int isScope() const { return category | SCOPE; }
    inline int isDAggr() const { return category | DAGGR; }
    inline int hasType() const { return category | TYPE; }

    Type category;

    Sym(Type category): category(category){}

#ifndef NDEBUG
    virtual void print(int indent)=0;
#endif
};

struct SymVal : public Sym
{
    string name;
    string type;

    SymVal(const char* symname, const char* type_name):
        Sym(Sym::VAL), name(symname), type(type_name){}

#ifndef NDEBUG
    virtual void print(int indent) {
        PRINT("%*s VAL %s:%s\n", indent, "", name.c_str(), type.c_str());
    }
#endif
};

struct SymVar : public Sym
{
    string name;
    string type;

    SymVar(const char* symname, const char* type_name):
        Sym(Sym::VAR), name(symname), type(type_name){}

#ifndef NDEBUG
    virtual void print(int indent) {
        PRINT("%*s VAR %s:%s\n", indent, "", name.c_str(), type.c_str());
    }
#endif
};

#include "trie.h"
struct SymScopeMembers
{
    trie_t* t;

    SymScopeMembers(){ trie_init(t); }

   ~SymScopeMembers()
   {
        //@todo trie_foreach(t, deleteSymScopeMember);
        trie_destroy(t);
   }

    void push(const char* symname, Sym* sym) {
        trie_store(t, symname, (size_t)sym);
    }

    Sym* get(const char* symname) {
        Sym* sym = NULL;
        size_t val;
        if (trie_find(t, symname, &val)) {
            sym = (Sym*)val;
        }
        return sym;
    }
};

struct SymScope : public Sym
{

    SymScope(Type category, SymScope* enclosing_scope): Sym(category)
    {
        this->enclosing_scope = enclosing_scope;
    }

    //const char* getScopeName();
    inline SymScope* getEnclosingScope() { return enclosing_scope; }
    void defineSym(Sym*);
    Sym* resolve(const char* symname);

    SymScope* enclosing_scope;
    SymScopeMembers members;

#ifndef NDEBUG
    virtual void print(int indent) {
        PRINT("%*s scope members:\n", indent, "");
    }
#endif
};

struct SymBlock : public SymScope
{
    SymBlock(SymScope* enclosing_scope):
        SymScope(Sym::PKG, enclosing_scope){}
};

struct SymPkg : public SymScope
{
    string name;

    SymPkg(const char* symname, SymScope* enclosing_scope):
        SymScope(Sym::PKG, enclosing_scope), name(symname){}

#ifndef NDEBUG
    virtual void print(int indent) {
        PRINT("%*s PKG\n", indent, "");
        SymScope::print(indent);
    }
#endif

private:
    SymPkg(const SymPkg&);
};


struct SymFunc : public SymScope
{
    string name;
    SymScope body;

    SymFunc(const char* symname, SymScope* enclosing_scope):
        SymScope(Sym::FUNC, enclosing_scope), name(symname),
        body(Sym::BLOCK, this) // ARGS are enclosing scope for body
    {
        this->defineSym(&body);
    }
};


struct SymTbl : public SymPkg
{
    void initTypeSystem();

    SymTbl();
};


#endif

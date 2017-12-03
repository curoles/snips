/**@file
 * @brief     AST.
 * @author    Igor Lesik
 * @copyright Igor Lesik 2011-2012.
 *
 * License:   Distributed under the Boost Software License, Version 1.0.
 *            (See http://www.boost.org/LICENSE_1_0.txt)
 *
 */
#pragma once
#ifndef COH_AST_H_INCLUDED
#define COH_AST_H_INCLUDED

#include <stdio.h>
#include <stdbool.h>

#include "vector.h"
#include "String.h"

typedef struct AST AST;

typedef AST* ASTList_ElemType;

struct ASTList
{
    vector_t v;
};
typedef struct ASTList ASTList;

static inline
void ASTList_create(ASTList* self) {
    vector_init(&self->v, sizeof(ASTList_ElemType));
}

static inline
void ASTList_destroy(ASTList* self) {
    vector_destroy(&self->v);
}

static inline
ASTList_ElemType ASTList_at(ASTList* self, size_t index) {
    return vector_at(ASTList_ElemType, self->v, index);
}

static inline
void ASTList_push_back(ASTList* self, ASTList_ElemType el) {
    vector_push_back(ASTList_ElemType, self->v, el);
}

static inline
ASTList_ElemType* ASTList_begin(ASTList* self) {
    return (ASTList_ElemType*)self->v.element + 0;
}

static inline
ASTList_ElemType* ASTList_end(ASTList* self) {
    return (ASTList_ElemType*)self->v.element + self->v.size;
}

static inline
ASTList_ElemType* ASTList_front(ASTList* self) { return ASTList_begin(self); }

static inline
ASTList_ElemType* ASTList_back(ASTList* self)  { return ASTList_end(self) - 1; }

static inline size_t ASTList_size(ASTList* self) { return self->v.size; }
static inline bool ASTList_isEmpty(ASTList* self) { return (ASTList_size(self) == 0); }

enum ASTokenType {
    TOKEN__BEGIN = 0,
    TOKEN_NIL = 0, // no root node
    #define ASTOKEN(name) TOKEN_##name
    #include "astoken.h"
    #undef ASTOKEN
    TOKEN__END
};
typedef enum ASTokenType ASTokenType;

struct ASToken
{
    ASTokenType type;
    String str;
};
typedef struct ASToken ASToken;

static inline
void ASToken_create(ASToken* self, ASTokenType type, const char* s)
{
    self->type = type;
    String_create(&self->str, 0, s);
}

static inline
void ASToken_destroy(ASToken* self)
{
    String_destroy(&self->str);
}

const char* ASToken_typeToString(ASTokenType type);


struct AST
{
    ASToken token;
    ASTList children;
};
typedef struct AST AST;

static inline
void AST_create(AST* self, ASTokenType token_type, const char* token_str)
{
    ASToken_create(&self->token, token_type, token_str);
    ASTList_create(&self->children);
}

static inline
AST* AST_new(ASTokenType token_type, const char* token_str)
{
    AST* self = calloc(1, sizeof(AST));
    AST_create(self, token_type, token_str);
    return self;
}

void AST_destroy(AST* self);


static inline
void AST_addChild(AST* self, AST* child) {
    ASTList_push_back(&self->children, child);
}

void AST_print(AST* self, FILE* f, int indent);
void AST_printChildren(AST* self, FILE* f, int indent);

#define AST_FOR_EACH(self, child) \
    for (child = ASTList_begin(&self->children); child < ASTList_end(&self->children); ++child)


#endif

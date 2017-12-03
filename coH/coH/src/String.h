/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012
 *
 */
#pragma once
#ifndef COH_STRING_H_INCLUDED
#define COH_STRING_H_INCLUDED

#include <string.h>
#include <assert.h>
#include <stdbool.h>

/** String interface.
 *
 */
struct String
{
    const char* p;

    size_t len;  // const. time vs strlen()
    size_t size; // allocated size, 0 - not allocated 
};
typedef struct String String;

#define EMPTY_STRING {0}

/** Create a String that uses string literal.
 *
 * @note use only with string literal:
 * String_create(s, "string_literal");
 */
static inline
const char*
String_createFromLiteral(String* self, const char* str)
{
    assert(self);
    assert(str);
    self->p = str;
    self->size = 0;   // not allocated, points to literal
    self->len = strlen(self->p);

    return self->p;
}

/** Allocate storage for String.
 *
 * @param self
 * @param size storage size to be allocated
 * @param str  string to copy, if NULL then create empty string
 */
const char*
String_create(String* self, size_t size, const char* str);

/** Free String resources.
 *
 */
void
String_destroy(String* self);

static inline
bool
String_isEmpty(String* self)
{
    assert(self);
    return !self->p || 0 == self->len;
}

const char*
String_append(String* self, const char* tail);

#endif //  COH_STRING_H_INCLUDED

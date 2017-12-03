/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012
 *
 */
#include "String.h"

#include <stdlib.h>

#include "COH.h"

/** Allocate storage for String.
 *
 * @param self
 * @param size storage size to be allocated, 0 for auto sizing
 * @param str  string to copy, if NULL then create empty string
 */
const char*
String_create(String* self, size_t size, const char* str)
{
    if (str && (strlen(str)+1ul) > size)
    {
        size = strlen(str) + 1ul;
    }

    assert(self);
    assert(size);
    
    self->p = (char*)calloc(size, sizeof(char));
    assert(self->p);

    self->size = size;

    if (str)
        strncpy((char*)self->p, str, size);
    else
        strncpy((char*)self->p, "", size);

    self->len = strlen(self->p);

    return self->p;
}

/** Free String resources.
 *
 */
void
String_destroy(String* self)
{
    assert(self);
    assert(self->p);

    if (self->size) // not literal
    {
        free((char*)self->p);
    }

    self->size = 0;
    self->p    = NULL;
    self->len  = 0;
}

#ifdef UNIT_TEST
BEGIN_UNIT_TEST(String,__LINE__)
    String s;
    String_createFromLiteral(&s, "12345");
    assert(s.len == 5);
    String_destroy(&s);
    assert(s.p == NULL);
    String_create(&s, 0, "12345");
    assert(s.len == 5);
    String_destroy(&s);
    assert(s.p == NULL);
END_UNIT_TEST
#endif


const char*
String_append(String* self, const char* tail)
{
    size_t old_len;
    size_t tail_len;

    assert(self);
    assert(tail);

    old_len = self->len;
    tail_len = strlen(tail);

    assert(tail_len < 1024);

    if (self->p == NULL)
    {
        String_create(self, 0, tail);
        return self->p;
    }

    // allocate buffer if it is literal
    if (self->size == 0)
    {
        String_create(self, old_len + tail_len + 128, self->p); 
    }
    // allocate more space if needed
    else if (self->size <= (old_len + tail_len))
    {
        self->p = realloc((void*)self->p, self->len + strlen(tail) + 128); 
        self->len = strlen(self->p);
    }

    {
    char* p = (char*)self->p;
    strncpy(p + old_len, tail, tail_len);
    self->len = old_len + tail_len;
    p[self->len] = '\0';
    }

    return self->p;
}


#ifdef UNIT_TEST
BEGIN_UNIT_TEST(String_append,__LINE__)
    String s = EMPTY_STRING;
    String_append(&s, "12345");
    assert(s.len == 5);
    String_destroy(&s);
    assert(s.p == NULL);
    String_create(&s, 0, "12345");
    assert(s.len == 5);
    String_append(&s, "678");
    assert(s.len == 8);
    String_append(&s, "9a");
    assert(s.len == 10);
    String_destroy(&s);
    assert(s.p == NULL);
END_UNIT_TEST
#endif





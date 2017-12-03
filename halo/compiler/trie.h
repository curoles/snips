/**@file
 *  Authors:   Igor Lesik.
 *  Copyright: Igor Lesik 2009.
 *  License:   Distributed under the Boost Software License, Version 1.0.
 *            (See http://www.boost.org/LICENSE_1_0.txt)
 *
 *  Trie data structure.
 *
 */
#pragma once
#ifndef TRIE_H_INCLUDED
#define TRIE_H_INCLUDED

#include <assert.h>
#include <string.h>
#include <stdint.h>

#include "vector.h"

typedef vector_t trie_t;

void trie_init(trie_t* t);

void trie_store(trie_t* t, const char* str, size_t val);

int trie_find(trie_t* t, const char* str, size_t* val);

void trie_destroy(trie_t* t);

#ifdef TRIE_UNIT_TEST

void trie_print(trie_t* t, size_t level);

void trie_unit_test();
#endif // TRIE_UNIT_TEST

#endif


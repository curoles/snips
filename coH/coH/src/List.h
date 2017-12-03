/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012
 *
 */
#pragma once
#ifndef COH_LIST_H_INCLUDED
#define COH_LIST_H_INCLUDED

#include <string.h>
#include <assert.h>

typedef struct List* List;
typedef void* listel_t;

#define EMPTY_LIST ((List)NULL)

/** List interface.
 *
 */
struct List
{
    listel_t first_el;

    List rest;
};

static inline int List_is_empty(List self)
{
    return self == EMPTY_LIST;
}

List List_create(listel_t el, ...);

void List_destroy(List* list);

List List_push_front(List self, listel_t el);

void List_foreach(
    List self,
    void apply(listel_t* el, void* context),
    void* context
);

size_t List_size(List self);

#define DEF_LIST_PRINTER(fun_name,T,frmt)  \
void fun_name (listel_t* el, void* cntx) {  \
    printf((const char*)frmt, (T)*el); }

#endif //  COH_LIST_H_INCLUDED

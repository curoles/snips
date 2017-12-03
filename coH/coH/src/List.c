/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012
 *
 */
#include "List.h"

#include <stdlib.h>

#include "COH.h"

List List_push_front(List self, listel_t new_el)
{
    List list = EMPTY_LIST;

    list = calloc(1, sizeof(struct List));
    assert(list);
    list->first_el = new_el;
    list->rest = self;

    return list;
}

#ifdef UNIT_TEST
static DEF_LIST_PRINTER(printListOfStrings, char*, "%s ")

BEGIN_UNIT_TEST(List_push_front,__LINE__)
    List list = EMPTY_LIST;
    assert(List_is_empty(list));
    list = List_push_front(list, "one");
    list = List_push_front(list, "two");
    list = List_push_front(list, "three");
    assert(!List_is_empty(list));
    assert(List_size(list) == 3);
    List_foreach(list, printListOfStrings, NULL);
    List_destroy(&list);
    assert(List_size(list) == 0);
END_UNIT_TEST
#endif

void List_destroy(List* list)
{
    List next;

    assert(list);
    for ( ; *list; *list = next)
    {
        next = (*list)->rest;
        free(*list);
    }
}

void List_foreach(
    List list,
    void apply(listel_t* el, void* context),
    void* context
)
{
    assert(apply);
    for ( ; list; list = list->rest)
    {
        apply(&list->first_el, context);
    }
}

size_t List_size(List list)
{
    size_t size = 0;

    for ( ; list; ++size, list = list->rest){}

    return size;
}

#ifdef UNIT_TEST
static struct List l__1 = {"one",NULL};
static struct List l__2 = {"two",&l__1};

BEGIN_UNIT_TEST(List_create_at_compile_time,__LINE__)
    List list = &l__2;
    assert(!List_is_empty(list));
    assert(List_size(list) == 2);
    List_foreach(list, printListOfStrings, NULL);
END_UNIT_TEST
#endif

#include <stdarg.h>

List List_create(listel_t el, ...)
{
    va_list ap;
    List list = EMPTY_LIST;
    List* p = &list;

    va_start(ap, el);
    for (; el; el = va_arg(ap, listel_t))
    {
        *p = calloc(1, sizeof(struct List));
        (*p)->first_el = el;
        p = &(*p)->rest;
    }
    *p = NULL;
    va_end(ap);
    return list;
}

#ifdef UNIT_TEST
BEGIN_UNIT_TEST(List_create,__LINE__)
    List list = List_create("one", "two", "three", NULL);
    assert(!List_is_empty(list));
    assert(List_size(list) == 3);
    List_foreach(list, printListOfStrings, NULL);
    List_destroy(&list);
END_UNIT_TEST
#endif


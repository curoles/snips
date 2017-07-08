#pragma once

#ifndef IGR_ALLOC_H_INCLUDED
#define IGR_ALLOC_H_INCLUDED

#include "igr.h"

typedef uint arena_t;

void* allocate(
    ulong size,
    arena_t arenaId
);

void deallocate(
    arena_t arenaId
);

#define NEW(p, a) ((p) = allocate(sizeof(*(p)), (a)))

#define NEW0(p, a) memset(NEW((p),(a)), 0, sizeof(*(p)))

bool test_allocate();

void show_allocations();

#endif /*IGR_ALLOC_H_INCLUDED*/

#include "alloc.h"

#include <assert.h>

#include "igr.h"

typedef
struct ArenaBlock {
    struct ArenaBlock* next;
    byte* limit;
    byte* avail;
} ArenaBlock;

static ArenaBlock g_firstBlock[] = {
    {NULL}, {NULL}, {NULL}
};

static ArenaBlock* g_arena[] = {
    &g_firstBlock[0], &g_firstBlock[1], &g_firstBlock[2]
};

union MemAlign {
    long l;
    char* p;
    double d;
    int (*f)(void);
};

static
ulong roundup(ulong size, ulong align)
{
    return size + (size % align);
};

void* allocate(
    ulong size,
    arena_t arena_id
)
{
    ArenaBlock* arena = g_arena[arena_id];

    assert(arena_id < sizeof_array(g_arena));

    size = roundup(size, sizeof(union MemAlign));

    while ((arena->avail + size) > arena->limit) {

    }

    arena->avail += size;

    return arena->avail - size;
}


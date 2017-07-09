#include "alloc.h"

#include <assert.h>

#include "igr.h"
#include "print.h"

#define BLOCK_MIN_SIZE (10*1024)

union MemAlign {
    long l;
    char* p;
    double d;
    int (*f)(void);
};

typedef
struct ArenaBlock {
    struct ArenaBlock* next;
    byte* limit;
    byte* avail;
} ArenaBlock
__attribute__ ((aligned (sizeof(union MemAlign))));

static ArenaBlock g_firstBlock[] = {
    {NULL}, {NULL}, {NULL}
};

static ArenaBlock* g_arena[] = {
    &g_firstBlock[0], &g_firstBlock[1], &g_firstBlock[2]
};

static ArenaBlock* g_freeBlocks = NULL;


static inline
ulong roundup(ulong size, ulong align)
{
    assert(align > 0);
    ulong reminder = size % align;
    return (reminder == 0)? size : size + align - reminder;
};

#include <stdlib.h> // malloc

static
ArenaBlock* allocate_new_block(ArenaBlock* block, ulong size)
{
    ulong new_block_size = sizeof(ArenaBlock) + size + BLOCK_MIN_SIZE;
    block->next = malloc(new_block_size);
    ArenaBlock* new_block = block->next;

    //DBG("new block allocated %p\n", new_block);

    //assert(new_block != NULL);

    if (new_block == NULL) {
        dbg_error("insufficient memory, requested %lu\n", new_block_size);
        exit(FAIL);
    }

    new_block->limit = (byte*)new_block + new_block_size;

    return new_block;
};

static
ArenaBlock* get_new_block(ArenaBlock* block, ulong size)
{
    //DBG("get new block size=%lu\n", size);

    assert(block != NULL);

    ArenaBlock* new_block = NULL;

    if ((block->next = g_freeBlocks) != NULL) { // check available free blocks
        g_freeBlocks = g_freeBlocks->next; // pop front
        new_block = block->next;
    } else {
        new_block = allocate_new_block(block, size);
    }

    assert(new_block != NULL);

    new_block->next = NULL;
    new_block->avail = (byte*)((ArenaBlock*)new_block + 1);

    return new_block;
};

void* allocate(
    ulong size,
    arena_t arena_id
)
{
    assert(arena_id < sizeof_array(g_arena));

    ArenaBlock* block = g_arena[arena_id];

    size = roundup(size, sizeof(union MemAlign));

    while ((block->avail + size) > block->limit) {
        g_arena[arena_id] = block = get_new_block(block, size);
    }

    block->avail += size; // point to free space

    return block->avail - size;
}

void deallocate(
    arena_t arena_id
)
{
    DBG("deallocate arena %u\n", arena_id);

    assert(arena_id < sizeof_array(g_arena));

    g_arena[arena_id]->next = g_freeBlocks;     // add free blocks to used blocks
    g_freeBlocks = g_firstBlock[arena_id].next; // free = used by ptr assignment
    g_firstBlock[arena_id].next = NULL;         // collapse list of used blocks
    g_arena[arena_id] = &g_firstBlock[arena_id];// point current used block to head
}

void delete_all_allocations()
{
    // Move all blocks into the free list.
    for (int arena_id = 0; arena_id < sizeof_array(g_arena); ++arena_id) {
        deallocate(arena_id);
    }

    ArenaBlock* block = g_freeBlocks;

    while (block != NULL) {
        ArenaBlock* next_block = block->next;
        if (block->limit != NULL) { // do not delete first/head block
            free(block);
        }
        block = next_block;
    }
}

static
void inspect_allocations()
{
    const ArenaBlock* block = g_freeBlocks;


    void print_block(const char* m, const ArenaBlock* blk) {
        ulong blk_size = (ulong)blk->limit - (ulong)blk - sizeof(ArenaBlock);
        ulong blk_used = (ulong)blk->avail - (ulong)blk - sizeof(ArenaBlock);
        uint blk_used_percent = (((double)blk_used)/blk_size)*100;
        print_note("%s %p [%p..%p] %8lu %8lu %3u%% ->%p\n",
            m, blk, blk->avail, blk->limit,
            blk_size, blk_used, blk_used_percent, blk->next);
    }

    print_note("Blocks:\n");

    while (block != NULL) {
        if (block->limit != NULL){ // do not show first/head block
            print_block("-", block);
        }
        block = block->next;
    }

    for (int arena_id = 0; arena_id < sizeof_array(g_firstBlock); ++arena_id) {

        block = g_firstBlock[arena_id].next;
    
        while (block != NULL) {
            print_block("+", block);
            block = block->next;
        }
    }

}

void show_allocations()
{
    inspect_allocations();
}


bool test_allocate()
{
#if (0)
    inspect_allocations(0);
    void* mem = allocate(16, 0);
    assert(mem != NULL);
    inspect_allocations();
    mem = allocate(161, 0);
    assert(mem != NULL);
    inspect_allocations();
    mem = allocate(BLOCK_MIN_SIZE, 0);
    assert(mem != NULL);
    inspect_allocations();
    deallocate(0);
    inspect_allocations();

    mem = allocate(32, 0);
    inspect_allocations();
#endif
    return true;
}


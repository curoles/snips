#include "selfcheck.h"

#include <assert.h>

#include "alloc.h"

static
bool test_allocate()
{
    void* mem = allocate(16, 0);
    assert(mem != NULL);
    return true;
}

bool selfcheck()
{
    test_allocate();
    return false;
}

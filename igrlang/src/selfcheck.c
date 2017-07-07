#include "selfcheck.h"

#include <assert.h>

#include "alloc.h"
#include "print.h"


bool selfcheck()
{
    if (!test_allocate()) {
        print_error("Test 'allocate' FAILED\n");
        return false;
    }

    return true;
}

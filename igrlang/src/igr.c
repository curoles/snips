#include <stdio.h>

#include "selfcheck.h"
#include "print.h"

enum RetStatus {SUCCESS=0, FAIL=1};

int main(int argc, const char* argv[])
{
    if (!selfcheck()) {
        printf("Self checking test %sFAILED%s\n",
            prtclr(PCLR_BOLD_RED), prtclr(PCLR_NONE));
        return FAIL;
    }
    return SUCCESS;
}

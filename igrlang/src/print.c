#include "print.h"

const char* prtclr(PrintColor color)
{
    switch (color){
        case PCLR_BLACK: return "\x1B[30m";
        case PCLR_RED: return "\x1B[31m";
        case PCLR_BOLD_RED: return "\x1B[1;31m";
        default: return "\x1B[0m";
    }

    return "\x1B[0m";
}


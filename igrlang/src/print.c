#include "print.h"

#include <unistd.h>

#include "igr.h"

static bool has_colors = false;

void enable_print_colors(bool enable) {
    has_colors = enable && isatty(STDERR_FILENO) && isatty(STDOUT_FILENO);
};

const char* prtclr(PrintColor color)
{
    if (!has_colors) return "";

    switch (color){
        case PCLR_BOLD: return "\x1B[1m";
        case PCLR_BLACK: return "\x1B[30m";
        case PCLR_RED: return "\x1B[31m";
        case PCLR_GREEN: return "\x1B[32m";
        case PCLR_BOLD_RED: return "\x1B[1;31m";
        case PCLR_CYAN: return "\x1B[36m";
        default: return "\x1B[0m";
    }

    return "\x1B[0m";
}


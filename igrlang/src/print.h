#pragma once

#ifndef IGR_PRINT_H_INCLUDED
#define IGR_PRINT_H_INCLUDED

#include <stdio.h>

#include "igr.h"

typedef
enum PrintColor {
    PCLR_NONE = 0,
    PCLR_BOLD = 1,
    PCLR_BLACK = 30, PCLR_BBLACK = 40,
    PCLR_RED = 31, PCLR_BRED = 41, PCLR_BOLD_RED = 131,
    PCLR_GREEN = 32, PCLR_BGREEN = 42,
    PCLR_YELLOW = 33, PCLR_BYELLOW = 43,
    PCLR_BLUE = 34, PCLR_BBLUE = 44,
    PCLR_MAGENTA = 35, PCLR_BMAGENTA = 45,
    PCLR_CYAN = 36, PCLR_BCYAN = 46,
    PCLR_WHITE = 37, PCLR_BWHITE = 47
} PrintColor;

const char* prtclr(PrintColor color);

void enable_print_colors(bool enable);

#define DBG_LEVEL 3

#define dbg_error(args...) \
fprintf(stderr, "%s"__FILE__":%d: %serror: %s", \
prtclr(PCLR_BOLD),__LINE__,prtclr(PCLR_RED),prtclr(PCLR_NONE)); \
fprintf(stderr, args)

#define dbg_warn(args...) \
fprintf(stderr, "%s"__FILE__":%d: %swarning: %s", \
prtclr(PCLR_BOLD),__LINE__,prtclr(PCLR_YELLOW),prtclr(PCLR_NONE)); \
fprintf(stderr, args)

#define dbg_note(args...) \
fprintf(stderr, "%s"__FILE__":%d: %snote: %s", \
prtclr(PCLR_BOLD),__LINE__,prtclr(PCLR_CYAN),prtclr(PCLR_NONE)); \
fprintf(stderr, args)

#if (DBG_LEVEL >= 3)
#define DBG(args...) \
fprintf(stderr, "%s"__FILE__":%d: %sdbg: %s", \
prtclr(PCLR_BOLD),__LINE__,prtclr(PCLR_GREEN),prtclr(PCLR_NONE)); \
fprintf(stderr, args)
#else
#define DBG(args...)
#endif


#define print_error(args...) \
fprintf(stdout, "%sError: %s", \
prtclr(PCLR_BOLD_RED),prtclr(PCLR_NONE)); \
fprintf(stdout, args)

#define print_note(args...) \
fprintf(stdout, args)

#endif /*IGR_PRINT_H_INCLUDED*/

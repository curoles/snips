#pragma once

#ifndef IGR_PRINT_H_INCLUDED
#define IGR_PRINT_H_INCLUDED

typedef
enum PrintColor {
    PCLR_NONE = 0,
    PCLR_BOLD = 1,
    PCLR_BLACK = 30, PCLR_BBLACK = 40,
    PCLR_RED = 31, PCLR_BRED = 41, PCLR_BOLD_RED = 131,
    PCLR_GREEN = 32, PCLR_BGREEN = 42,
    PCLR_YELLOW = 33, PCLR_BYELLOW = 43,
    PCLR_BLUE = 34, PCLR_BBLUE = 44
} PrintColor;

const char* prtclr(PrintColor color);

#endif /*IGR_PRINT_H_INCLUDED*/

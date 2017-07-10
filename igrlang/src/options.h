#pragma once

#ifndef IGR_OPTIONS_H_INCLUDED
#define IGR_OPTIONS_H_INCLUDED

#include "igr.h"

typedef
struct Options
{
    int show_mem_alloc;
    int show_str_dist;
}
Options;

bool parse_options(int argc, const char* argv[]);

Options* get_options();

#endif /*IGR_OPTIONS_H_INCLUDED*/

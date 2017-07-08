#pragma once

#ifndef IGR_OPTIONS_H_INCLUDED
#define IGR_OPTIONS_H_INCLUDED

typedef
struct Options
{
  int show_mem_alloc;
}
Options;

int parse_options(int argc, const char* argv[]);

Options* get_options();

#endif /*IGR_OPTIONS_H_INCLUDED*/

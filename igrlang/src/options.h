/**@file
 * @brief     Compiler options
 * @author    Igor Lesik 2017
 * @copyright Igor Lesik 2017
 *
 *
 *
 */
#pragma once

#ifndef IGR_OPTIONS_H_INCLUDED
#define IGR_OPTIONS_H_INCLUDED

#include "igr.h"

/** All options as data members of one big structure.
 *
 *
 */
typedef
struct Options
{
    char* input_file;
    char* output_file;
    char* target;
    bool  show_mem_alloc;
    bool  show_str_dist;
}
Options;

/** Parse command line arguments and initialize options.
 *
 */
bool parse_options(int argc, const char* argv[]);

/** Get instance of the Options structure.
 *
 */
Options* get_options();

#endif /*IGR_OPTIONS_H_INCLUDED*/

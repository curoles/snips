/**@file
 * @brief     Configuration and options.
 * @author    Igor Lesik
 * @copyright Igor Lesik 2011-2012.
 *
 * Parse command line options.
 */
#pragma once
#ifndef COH_CFG_H_INCLUDED
#define COH_CFG_H_INCLUDED

#include <stdbool.h>

#include "String.h"


bool Cfg_parseCmdLineArgs(int argc, char** argv);
void Cfg_destroy();

extern String Cfg_input_file;
extern String Cfg_c_output_file;
extern String Cfg_h_output_file;
extern String Cfg_a_output_file;
extern String Cfg_output_dir;

#endif


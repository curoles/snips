/**@file
 * Configuration parameters.
 * Copyright (C) 2011 Igor Lesik.
 *
 * Reads command line options and configuration file.
 */
#pragma once
#ifndef HALO_CFG_H_INCLUDED
#define HALO_CFG_H_INCLUDED

#include <string.h>
#include <stdint.h>
#include "ztring.h"

class Cfg
{

public:
    static const char* inputFile() { return m_input_file_name; }
    static const char* outputFile() { return m_output_file_name; }

    static void parseCmdLineArgs(int argc, char** argv);

private:

    static string m_input_file_name;
    static string m_output_file_name;
};

#endif // HALO_CFG_H_INCLUDED


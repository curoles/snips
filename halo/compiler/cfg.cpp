/**@file
 * Configuration parameters.
 * Copyright (C) 2011 Igor Lesik.
 *
 * Reads command line options and configuration file.
 */
#include "cfg.h"

#include <stdlib.h>
#include <getopt.h>
#include "debug.h"

string Cfg::m_input_file_name;
string Cfg::m_output_file_name;


static const char* halo_args_usage = 
    "Usage:\n"
    "[options] [input file]"
    "\n"
    "\t[program file]   - name of the input file.\n"
    "\t-h               - this help message.\n"
    "\t-o output file   - .\n"
    "\n"
    ;


/** Parse command line options.
 *
 * getopt, if followed by ":" indicates that it takes arguments
 */
void Cfg::parseCmdLineArgs(int argc, char** argv)
{
    int c;
    int errflag = 0;
    extern char *optarg;
    extern int optind, optopt;

    while ((c = getopt(argc, argv, "ho:")) != -1)
    {
        switch(c) 
        {
            case 'o':
                m_output_file_name = optarg;
                PRINT("Output file:%s\n", m_output_file_name.c_str());
                break;
             case 'h':
                printf("%s", halo_args_usage);
                exit(2);
                break;
            case ':':
                PRINT("Option -%c requires an operand\n", optopt);
                errflag++;
                break;
            case '?':
                PRINT("Unrecognized option: -%c\n", optopt);
                errflag++;
                break;
            default:
                break;
        }
    }

    if (errflag) {
        PRINT("%s", halo_args_usage);
        exit(2);
    }

    if (optind < argc) {
        m_input_file_name = argv[optind];
        PRINT("Input file:%s\n", m_input_file_name.c_str());
    }
    else {
        PRINT("No input file\n");
    }

    //if (m_output_file_name.empty()) {
    //    m_output_file_name = m_input_file_name;
    //    m_output_file_name.append(".o");
    //}
}

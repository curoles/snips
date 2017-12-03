/**@file
 * @brief     Configuration and options.
 * @author    Igor Lesik
 * @copyright Igor Lesik 2011-2012.
 *
 * Parse command line options.
 */
#include "cfg.h"

#include <stdlib.h>
#include <getopt.h>
#include "debug.h"

String Cfg_input_file;
String Cfg_output_dir;
String Cfg_c_output_file;
String Cfg_h_output_file;
String Cfg_a_output_file;

static const char* coH_args_usage = 
    "Usage:\n"
    "[options] [input file]"
    "\n"
    "\t[program file]   - name of the input file.\n"
    "\t-h               - this help message.\n"
    "\t-o output_dir    - output directory.\n"
    "\n"
    ;

static void Cfg_init()
{
    String_createFromLiteral(&Cfg_output_dir, "./build");
}

void Cfg_destroy()
{
    String_destroy(&Cfg_input_file);
    String_destroy(&Cfg_output_dir);
    String_destroy(&Cfg_c_output_file);
    String_destroy(&Cfg_h_output_file);
    String_destroy(&Cfg_a_output_file);
}

static inline
const char* fileBasename(const char* path)
{
    char* base = strrchr(path, '/');
    return base ? base+1 : path;
}

static bool Cfg_postProcessOptions()
{
    const char* infile = NULL;

    if (String_isEmpty(&Cfg_input_file))
    {
        return true;
    }

    infile = fileBasename(Cfg_input_file.p);

    if (strlen(infile) < 4
        || strcmp(".coh", infile + strlen(infile) - 4))
    {
        PRINT("Error: file extention is not '.coh'\n");
        return false;
    } 

    String_create(&Cfg_c_output_file, 128, Cfg_output_dir.p);
    String_create(&Cfg_h_output_file, 128, Cfg_output_dir.p);
    String_create(&Cfg_a_output_file, 128, Cfg_output_dir.p);
    String_append(&Cfg_c_output_file, "/");
    String_append(&Cfg_h_output_file, "/");
    String_append(&Cfg_a_output_file, "/");
    String_append(&Cfg_c_output_file, infile); Cfg_c_output_file.len -= 4;
    String_append(&Cfg_h_output_file, infile); Cfg_h_output_file.len -= 4;
    String_append(&Cfg_a_output_file, infile); Cfg_a_output_file.len -= 4;
    String_append(&Cfg_c_output_file, ".c");
    String_append(&Cfg_h_output_file, ".h");
    String_append(&Cfg_a_output_file, ".ast");

    return true;
}

/** Parse command line options.
 *
 * getopt, if followed by ":" indicates that it takes arguments
 */
bool Cfg_parseCmdLineArgs(int argc, char** argv)
{
    int c;
    int errflag = 0;
    extern char *optarg;
    extern int optind, optopt;

    Cfg_init();

    while ((c = getopt(argc, argv, "ho:")) != -1)
    {
        switch(c) 
        {
            case 'o':
                String_create(&Cfg_output_dir, 0, optarg);
                PRINT("Output dir:%s\n", Cfg_output_dir.p);
                break;
             case 'h':
                printf("%s", coH_args_usage);
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
        PRINT("%s", coH_args_usage);
        exit(2);
    }

    if (optind < argc) {
        String_create(&Cfg_input_file, 0, argv[optind]);
        PRINT("Input file:%s\n", Cfg_input_file.p);
    }
    else {
        PRINT("No input file\n");
    }

    return Cfg_postProcessOptions();
}

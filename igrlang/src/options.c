/**@file
 * @brief     Compiler options
 * @author    Igor Lesik 2017
 * @copyright Igor Lesik 2017
 *
 *
 *
 */
#include "options.h"

// https://www.gnu.org/software/libc/manual/html_node/Argp.html
#include <argp.h>
#include <string.h>

#include "print.h"
#include "string.h"


// Global variable with version string expected by Argp.
//
const char* argp_program_version = "igr 1.0";

const char* argp_program_bug_address = "<bug@???.org>";

/* Program documentation. */
static char doc[] =
  "IGR compiler";

/* A description of the arguments we accept. */
static char args_doc[] = "INPUT1";

enum OptKey {
    OPT_SHOW_MEM_ALLOC = 1000,
    OPT_SHOW_STR_DIST
};

/* The options we understand. */
static struct argp_option options[] = {
  {"target",  't', 0, 0,
       "Target architecture" },
  {"output",  'o', 0, 0,
       "Output file" },
  {"show-mem-alloc",  OPT_SHOW_MEM_ALLOC, 0, 0,
       "Show memory allocated for compilation" },
  {"show-str-disr",  OPT_SHOW_STR_DIST, 0, 0,
       "Show allocated strings hash distribution" },
  { 0 }
};


static Options g_options;

Options* get_options(){
    return &g_options;
}

static
void set_default_options()
{
    g_options.input_file = "";
    g_options.output_file = "";
    g_options.target = "x86";
    g_options.show_mem_alloc = false;
    g_options.show_str_dist = false;
}

static error_t
parse_opt (int key, char *arg, struct argp_state *state)
{
    /* Get the input argument from argp_parse, which we
       know is a pointer to our arguments structure. */
    Options *op = state->input;

  switch (key)
    {
/*
    case 'q': case 's':
      arguments->silent = 1;
      break;
*/
    case 't':
      op->target = string(arg);
      break;
    case 'i':
      op->input_file = string(arg);
      break;
    case 'o':
      op->output_file = string(arg);
      break;
/*
    case 'r':
      arguments->repeat_count = arg ? atoi (arg) : 10;
      break;
*/
    case OPT_SHOW_MEM_ALLOC:
      op->show_mem_alloc = true;
      break;

    case OPT_SHOW_STR_DIST:
      op->show_str_dist = true;
      break;

    case ARGP_KEY_NO_ARGS:
      argp_usage (state);

    case ARGP_KEY_ARG:
      /* Here we know that state->arg_num == 0, since we
         force argument parsing to end before any more arguments can
         get here. */
      op->input_file = string(arg);

      /* Now we consume all the rest of the arguments.
         state->next is the index in state->argv of the
         next argument to be parsed, which is the first string
         we’re interested in, so we can just use
         &state->argv[state->next] as the value for
         arguments->strings.

         In addition, by setting state->next to the end
         of the arguments, we can force argp to stop parsing here and
         return. */
      //arguments->strings = &state->argv[state->next];
      state->next = state->argc; // stop parsing

      break;

    case ARGP_KEY_END:
      if (strlen(op->input_file) == 0) {
          print_error("input file not provided\n");
          argp_usage(state);
      }
      //if (state->arg_num < 2)
        /* Not enough arguments. */
        //argp_usage (state);
      break;

    case ARGP_KEY_INIT:/* Passed in before any parsing is done */
    case ARGP_KEY_FINI:/* Passed in when parsing has successfully been completed */
    case ARGP_KEY_SUCCESS:
    case ARGP_KEY_ERROR:/* Passed in if an error occurs.  */
    break;

    default:
      print_error("unknown option %d %s\n", key, arg);
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}

static struct argp argp = { options, parse_opt, args_doc, doc };

bool parse_options(int argc, const char* argv[])
{
    set_default_options();

    argp_parse(&argp, argc, (char**)argv, 0, 0, &g_options);

    dbg_note("Command line arguments are parsed\n");

    return true;
}

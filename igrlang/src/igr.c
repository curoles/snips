/**@file
 * @brief     Compiler main entry point
 * @author    Igor Lesik 2017
 * @copyright Igor Lesik 2017
 *
 *
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "igr.h"
#include "selfcheck.h"
#include "print.h"
#include "options.h"
#include "alloc.h"
#include "string.h"

typedef struct CompilerData {
    FILE* input_file;
    FILE* output_file;

    Options* op;
}
CompilerData;

static CompilerData data = {0,};

static
void cleanup_on_exit()
{
    static bool already_cleaned = false;

    if (already_cleaned) return;
    already_cleaned = true;

    dbg_note("cleanup on exit\n");

    if (data.input_file) {
        fclose(data.input_file);
        data.input_file = NULL;
    }

    if (data.output_file) {
        fclose(data.output_file);
        data.output_file = NULL;
    }

    delete_all_allocations();
}

static
bool pre_init()
{
    // Install cleanup-on-exit callback.
    // https://www.gnu.org/software/libc/manual/html_node/Cleanups-on-Exit.html
    if (FAIL == atexit(cleanup_on_exit)) {
        print_error("can't register callback function for 'atexit'\n");
        return false;
    }

    enable_print_colors(true);

    data.op = get_options();

    return true;
}

static
bool init()
{
    if (!selfcheck()) {
        print_error("Self checking test FAILED\n");
        return false;
    }

    if ((data.input_file=fopen(data.op->input_file,"r")) == NULL) {
        print_error("can't open input file %s\n", data.op->input_file);
        return false;
    }

    if (strlen(data.op->output_file) == 0) {
        const char* filename = strrchr(data.op->input_file,'/')? : data.op->input_file;
        data.op->output_file = string_append(filename, ".s");
    }

    if ((data.output_file=fopen(data.op->output_file,"w")) == NULL) {
        print_error("can't open output file %s\n", data.op->output_file);
        return false;
    }


    return true;
}

static
bool on_finish()
{
    if (get_options()->show_str_dist) {
        show_string_hash_distribution(/*chunk=*/100);
    }

    if (get_options()->show_mem_alloc) {
        show_allocations();
    }

    return true;
}

void x86_gen_function(
    FILE* out
);


static
bool compile()
{
//TODO see page 306


    x86_gen_function(data.output_file);
    return true;
}

int main(int argc, const char* argv[])
{
    if (!pre_init()) {
        print_error("pre_init failed\n");
        return EXIT_FAILURE;
    }

    if (!parse_options(argc, argv)) {
        print_error("parse_options failed\n");
        return EXIT_FAILURE;
    }

    if (!init()) {
        print_error("init failed\n");
        return EXIT_FAILURE;
    }

    if (!compile()) {
        print_error("compile failed\n");
        return EXIT_FAILURE;
    }

    if (!on_finish()) {
        print_error("on_finish failed\n");
        return EXIT_FAILURE;
    }

    cleanup_on_exit();

    return EXIT_SUCCESS;
}

/*
//http://bisqwit.iki.fi/story/howto/openmp/

void test_opm()
{
int MAX_NUM=100,i,j,k;
#pragma omp parallel for default(shared) private(i, j, k)
for (i = 0; i < MAX_NUM; i++) {
     for (j = 0; j < MAX_NUM; j++) {
          for (k = 0; k < MAX_NUM; k++)
              ; //Y[i][j] += A[i][k] * B[k][j];
      }
}
}*/

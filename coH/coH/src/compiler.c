/**@file
 * @brief     Compiler.
 * @author    Igor Lesik.
 * @copyright Igor Lesik 2011-2012.
 *
 */
#include "compiler.h"

#include "cfg.h"
#include "debug.h"

#ifdef NDEBUG
    static inline void debug(uint64_t flags, const char* frmt, ...) {}
#else
    #define debug(flags, frmt, ...)\
        debugModule(DBG_COMPILE | flags, "compile", frmt, ##__VA_ARGS__)
#endif

void Compiler_create(Compiler* self)
{
    SrcReader_create(&self->srcReader);
    ErrReport_create(&self->errReport, &self->srcReader);
    Scanner_create(&self->scanner, &self->srcReader, &self->errReport);
    Parser_create(&self->parser, &self->srcReader, &self->errReport, &self->scanner);
    AST_create(&self->ast, TOKEN_NIL, "root");
    CodeGen_create(&self->codegen);
}

void Compiler_destroy(Compiler* self)
{
    CodeGen_destroy(&self->codegen);
    AST_destroy(&self->ast);
    Parser_destroy(&self->parser);
    Scanner_destroy(&self->scanner);
    ErrReport_destroy(&self->errReport);
    SrcReader_destroy(&self->srcReader);

    Cfg_destroy();
}


bool
Compiler_init(Compiler* self, int argc, char** argv)
{
    if (!Cfg_parseCmdLineArgs(argc, argv))
    {
        PRINT("Error: failed to read options\n");
        return false;
    }

    return true;
}

void
Compiler_printAST(Compiler* self)
{
    File f;
    File_create(&f);
    if (!File_open(&f, Cfg_a_output_file.p, "w")) {
        PRINT("Can't open AST output file %s\n", Cfg_a_output_file.p);
        return;
    }

    debug(DBG_L_DBG, "Open AST output file %s\n", Cfg_a_output_file.p);

    fprintf(f.fd, "\nAST tree:\n");
    AST_print(&self->ast, f.fd, /*indent=*/0);

    File_destroy(&f);
}

void
Compiler_generate(Compiler* self)
{
    File fh;
    File_create(&fh);
    if (!File_open(&fh, Cfg_h_output_file.p, "w")) {
        PRINT("Can't open .h output file %s\n", Cfg_h_output_file.p);
        return;
    }

    File fc;
    File_create(&fc);
    if (!File_open(&fc, Cfg_c_output_file.p, "w")) {
        PRINT("Can't open .c output file %s\n", Cfg_c_output_file.p);
        return;
    }

    CodeGen_run(&self->codegen, &self->ast, fh.fd, fc.fd);

    File_destroy(&fh);
    File_destroy(&fc);
}

bool
Compiler_run(Compiler* self)
{
    PRINT("Open %s\n", Cfg_input_file.p);
    PRINT("Open %s, %s\n", Cfg_c_output_file.p, Cfg_h_output_file.p);

    if (!SrcReader_open(&self->srcReader, Cfg_input_file.p))
    {
        PRINT("Error: Could not read source file %s\n", Cfg_input_file.p);
        return false;
    }

    Parser_parse(&self->parser, &self->ast);

    Compiler_generate(self);

    if (self->errReport.isError) {
        PRINT("Compilation failed\n");
    }
    else {
        PRINT("Compilation successful\n");
    }

    Compiler_printAST(self);

    return true;
}


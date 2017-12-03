/**@file
 * Compiler.
 * Copyright (C) 2011 Igor Lesik.
 *
 */
#include "compiler.h"

#include "cfg.h"
#include "debug.h"

Compiler::
Compiler():
    m_srcReader(),
    m_errReport(m_srcReader),
    m_scanner(m_srcReader, m_errReport),
    m_parser(m_srcReader, m_errReport, m_scanner),
    m_ast(AST::Token::TOKEN_NIL, "root")
{
}

Compiler::
~Compiler()
{
}

bool
Compiler::
init(int argc, char** argv)
{
    Cfg::parseCmdLineArgs(argc, argv);

    if (0 == strlen(Cfg::outputFile())) {
        PRINT("Error: Output file name not provided\n");
        return false;
    }

    return true;
}

bool
Compiler::
run()
{
    if (!m_srcReader.open(Cfg::inputFile())) {
        PRINT("Error: Could not read source file %s\n", Cfg::inputFile());
        return false;
    }

    m_parser.parse(m_ast);

    generate();

    if (m_errReport.isError()) {
        PRINT("Compilation failed\n");
    }
    else {
        PRINT("Compilation successful\n");
    }

    printAST();

    return true;
}

void
Compiler::
printAST()
{
    string filename(Cfg::outputFile());
    filename.stripSuffix();
    filename.append(".ast");

    File f;
    if (!f.open(filename.c_str(), "w")) {
        PRINT("Can't open AST output file %s\n", filename.c_str());
        return;
    }

    fprintf(f, "\nAST tree:\n");
    m_ast.print(f, 0);

}

void::
Compiler::
generate()
{
    string filename(Cfg::outputFile());
    filename.stripSuffix();
    filename.append(".ir");

    File f;
    if (!f.open(filename.c_str(), "w")) {
        PRINT("Can't open IR output file %s\n", filename.c_str());
        return;
    }

    m_codegen.run(f, m_ast);

}

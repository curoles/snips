/**@file
 * LL(1) Parser for syntax analysis.
 * Copyright (C) 2011 Igor Lesik.
 *
 */
#pragma once
#ifndef HALO_PARSER_H_INCLUDED
#define HALO_PARSER_H_INCLUDED

#include "defines.h"
#include "scan.h"

class SrcReader;
class ErrReport;
class AST;

/** The "syntax analyzer" or "parser" groups the tokens produced by the scanner
 * into syntactic structures.
 *
 */
class Parser
{
public:
    void parse(AST&);

    Parser(SrcReader&, ErrReport&, Scanner&);
   ~Parser();

private:
    inline void getSym() { m_scanner.getSym(sym); }

    inline void reportError(int errCode) { m_errReport.report(errCode); }
    
    void reportUnexpectedSymError(
        ScanSymType foundType,
        ScanSymType expectedTypes[],
        size_t size);

    inline bool isDone() { return (m_errReport.isError() || sym.type == SYM_EOF); }

private:
    static const bool CONSUME = true;
    static const bool SKIP_EOL = true;

    bool accept(
        ScanSymType type,
        int errCode = ERR_SYMBOL_EXPECTED,
        bool skip_eol = SKIP_EOL,
        bool consume = CONSUME
    );

    bool lookFor(ScanSymType types[], size_t size, ScanSymType& foundType);

    static inline bool isSkippableType(ScanSymType type) {
        return
            type == SYM_EOL_COMMENT
         || type == SYM_MULTI_COMMENT
         || type == SYM_EOL
       ;
    }


private:
    void parse_TopPackage(AST*);
    void parse_PackageBody(AST*);
    void parse_ValDeclaration(AST*);
    bool parse_Primary(AST*);
      bool parse_Literal(AST*, bool report_error = true);
      inline bool try_parse_Literal(AST* t) { return parse_Literal(t, false); }
    void parse_Expression(AST*);
      void parse_MultExpr(AST*);
    void parse_FuncDeclaration(AST*);

private:
    SrcReader& m_srcReader;
    ErrReport& m_errReport;
    Scanner&    m_scanner;

    Scanner::Symbol sym;
};


#endif

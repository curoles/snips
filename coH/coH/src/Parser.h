/**@file
 * @brief     LL(1) Parser for syntax analysis.
 * @author    Igor Lesik.
 * @copyright Igor Lesik 2011-2012.
 *
 * The "syntax analyzer" or "parser" groups the tokens produced by the scanner
 * into syntactic structures.
 */
#pragma once
#ifndef COH_PARSER_H_INCLUDED
#define COH_PARSER_H_INCLUDED

//#include "defines.h"
#include "Scanner.h"

typedef struct SrcReader SrcReader;
typedef struct ErrReport ErrReport;
typedef struct AST AST;

/** The "syntax analyzer" or "parser" groups the tokens produced by the scanner
 *  into syntactic structures.
 *
 */
struct Parser
{
    SrcReader* srcReader;
    ErrReport* errReport;
    Scanner*   scanner;

    Symbol sym;
};
typedef struct Parser Parser;



void Parser_create(Parser* self, SrcReader*, ErrReport*, Scanner*);
void Parser_destroy(Parser* self);
void Parser_parse(Parser* self, AST*);

#if 0

//static const bool PARSER_CONSUME = true;
//static const bool PARSER_SKIP_EOL = true;

private:
    inline void getSym() { m_scanner.getSym(sym); }

    inline void reportError(int errCode) { m_errReport.report(errCode); }
    
    void reportUnexpectedSymError(
        ScanSymType foundType,
        ScanSymType expectedTypes[],
        size_t size);

    inline bool isDone() { return (m_errReport.isError() || sym.type == SYM_EOF); }

private:


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


};
#endif

#endif

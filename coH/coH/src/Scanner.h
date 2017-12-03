/**@file
 * @brief     Scanner.
 * @author    Igor Lesik
 * @copyright 2011 Igor Lesik.
 *
 * The main task of the scanner is to provide some way of uniquely identifying
 * each successive token or symbol in the source code.
 *
 * The "lexical analyzer" or "scanner" fuses characters of the source text
 * into groups that logically make up the tokens of the language.
 *
 *
 */
#pragma once
#ifndef COH_SCAN_H_INCLUDED
#define COH_SCAN_H_INCLUDED

#include <stddef.h>

#include "SrcRead.h"
#include "ErrReport.h"
#include "trie.h"


/** Enumeration of symbols.
 *
 */
enum ScanSymType
{
#undef  DEF_SYM
#define DEF_SYM(name) SYM_##name,
    SYM__ILLEGAL = -1,
    #include "symcode.h"
    SYM__END
#undef  DEF_SYM
};
typedef enum ScanSymType ScanSymType;

/// Get symbol name by its ID.
const char* symName(size_t);

/// Symbol is a token of the language.
struct Symbol
{
    ScanSymType type;
    char name[SrcReader_LINEMAX + 1]; /// Textual representation of symbol.
};
typedef struct Symbol Symbol;

/// Language keyword.
struct Keyword
{
    const char* str;
    ScanSymType type;
};
typedef struct Keyword Keyword;

/// List of language keywords.
extern Keyword keywordList[];

/// White space (' ','\t','\r').
extern const char WS[3];

static inline bool isWS(char c)
{
    return c == WS[0] || c == WS[1] || c == WS[2];
}

/** The "lexical analyzer" or "scanner" fuses characters of the source text
 *  into groups that logically make up the tokens of the language.
 */
struct Scanner
{
    SrcReader* read;
    ErrReport* err;
    trie_t keywords;
};
typedef struct Scanner Scanner;

void Scanner_create(Scanner* self, SrcReader* srcReader, ErrReport* errReporter);
void Scanner_destroy();

static inline
void Scanner_reportError(Scanner* self, int errCode)
{
    ErrReport_report(self->err, errCode);
}

static inline
void Scanner_next(Scanner* self)
{
    SrcReader_nextChar(self->read);
}

bool Scanner_isValidNumberString(const char* s);

/// Obtain the next symbol in the source text.
void Scanner_getSym(Scanner* self, Symbol* sym);



#endif

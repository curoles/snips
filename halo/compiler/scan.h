/**@file
 * Scanner.
 * Copyright (C) 2011 Igor Lesik.
 *
 * The main task of the scanner is to provide some way of uniquely identifying
 * each successive token or symbol in the source code.
 *
 */
#pragma once
#ifndef HALO_SCAN_H_INCLUDED
#define HALO_SCAN_H_INCLUDED

#include "srcread.h"
#include "erreport.h"
#include "trie.h"

/** Enumeration of symbols.
 *
 */
enum ScanSymType {
#undef  DEF_SYM
#define DEF_SYM(name) SYM_##name,
    SYM__ILLEGAL = -1,
    #include "symcode.h"
    SYM__END
#undef  DEF_SYM
};

/// Get symbol name by its ID.
const char* symName(size_t);

/** The "lexical analyzer" or "scanner" fuses characters of the source text
 * into groups that logically make up the tokens of the language.  
 *
 * The main task of the scanner is to provide some way of uniquely identifying
 * each successive token or symbol in the source code.
 *
 */
class Scanner
{
public:
    struct Symbol
    {
        ScanSymType type;

        enum { LEXLEN = SrcReader::LINEMAX };
        char name[LEXLEN + 1]; /// Textual representation of symbol.
    };

    struct Keyword
    {
        const char* str;
        ScanSymType type;
    };

    Scanner(SrcReader&, ErrReport&);
   ~Scanner();

public:
    /// Obtain the next symbol in the source text.
    void getSym(Symbol& sym);

private:
    inline void next() { read.nextChar(); }

    inline void reportError(int errCode) { errp.report(errCode); }

    static bool isValidNumberString(const char*);

public:
    /// White space (' ','\t','\r').
    static const char WS[3];

private:
    static Keyword keywordList[];
    trie_t keywords;
    SrcReader& read;
    ErrReport& errp;
};


#endif

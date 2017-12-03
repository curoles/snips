/**@file
 * Scanner.
 * Copyright (C) 2011 Igor Lesik.
 *
 * The main task of the scanner is to provide some way of uniquely identifying
 * each successive token or symbol in the source code.
 *
 */
#include "scan.h"

#include "defines.h"
#include "srcread.h"
#include "debug.h"

#ifdef NDEBUG
    static inline void debug(uint64_t, const char*, ...) {}
#else
    #define debug(flags, frmt, ...)\
        debugModule(Dbg::SCAN | flags, "scan", frmt, ##__VA_ARGS__)
#endif

static const char* s_symName[] = {
#undef  DEF_SYM
#define DEF_SYM(name) #name,
#include "symcode.h"
#undef  DEF_SYM
};

/// Get symbol name by its ID.
const char* symName(size_t id)
{
    assert(id < sizeof_array(s_symName));

    return s_symName[id];
}

Scanner::Keyword Scanner::keywordList[] = {
    { "package", SYM_K_PACKAGE },
    { "import",  SYM_K_IMPORT  },
    { "func",    SYM_K_FUNC    },
    { "val",     SYM_K_VAL     },
    { "var",     SYM_K_VAR     },
    { "true",    SYM_K_TRUE    },
    { "false",   SYM_K_FALSE   },
};


const char Scanner::WS[3] = {' ', '\t', '\r'};

static inline bool isWS(char c) {
    return c == Scanner::WS[0] || c == Scanner::WS[1] || c == Scanner::WS[2];
}

Scanner::Scanner(SrcReader& sr, ErrReport& er):
    read(sr),
    errp(er)
{
    const size_t KEYWORDS_NUM = sizeof(keywordList)/sizeof(keywordList[0]);

    trie_init(&keywords);
    for (size_t i = 0; i < KEYWORDS_NUM; ++i) {
        trie_store(&keywords, keywordList[i].str, keywordList[i].type);
    }
}

Scanner::~Scanner()
{
    trie_destroy(&keywords);
}

inline bool isDigit(char c) {
    return ((c >= '0') && (c <= '9'));
}

inline bool isAlpha(char c) {
    return ((c >= 'A') && (c <= 'Z')) || ((c >= 'a') && (c <= 'z'));
}

inline bool canBeWord1stChar(char c) {
    return isAlpha(c) || c == '_' || c == '`';
}


inline bool canBeWordChar(char c) {
    return
        isAlpha(c)
     || isDigit(c)
     || (c == '_')
     || (c == '.')
     || (c == '`')
     ;
}

bool Scanner::isValidNumberString(const char* s /*, numType*/)
{
    bool isValid = true;

    size_t len = strlen(s);

    if (len == 0) {
        isValid = false;
    }
    else if (len == 1) {
        //type = dec
        isValid = isDigit(s[0]);
    }
    else {
        // dec: ** | 0d
        // hex: 0x
        // bin: 0b
        // oct: 0o
        // flt: *.

        if (s[0] != '0') { // dec or flt
            //type=dec
            //if found '.' then type=flt
        } else switch(s[1]) {
            case 'd': /*type=dec;*/ break;
            case 'x': /*type=hex;*/ break;
            case 'o': /*type=oct;*/ break;
            case 'b': /*type=bin;*/ break;
            case '.': /*type=flt;*/ break;
            default:
                PRINT("Error: number shall start with 0d|0x|0o|0b|0.\n");
                return false;
        }

        //do type specific checks
    }

    return isValid;
}
self
void Scanner::getSym(Symbol& sym)
{
#ifdef NDEBUG
    #define SINGLE(Type,c)\
        sym.type=Type; next();
#else
    #define SINGLE(Type,c)\
        sym.type=Type; sym.name[0]=c; sym.name[1]='\0'; next();
#endif

    //debug(Dbg::L2, "get with ch=%c\n", read.ch);

    // Ignore spaces between tokens
    while (isWS(read.ch))
        next();

    int len = 0;

    sym.name[0] = '\0';
    sym.type = SYM_UNKNOWN;

    if (canBeWord1stChar(read.ch)) // identifier, type or reserved word
    {
        do { 
            sym.name[len] = read.ch;
            len++;
            read.nextChar();
        } while(canBeWordChar(read.ch));

        sym.name[len] = '\0';

        size_t symType;
        int foundKeyWord = trie_find(&keywords, sym.name, &symType);

        if (foundKeyWord) {
            sym.type = (ScanSymType)symType;
        }
        else {
            sym.type = SYM_IDENTIFIER;
        }

        debug(Dbg::L0, "%s:%s\n", foundKeyWord? "keyword":"word", sym.name);
    }
    else if (isDigit(read.ch))
    {
        do {
            sym.name[len] = read.ch;
            len++;
            read.nextChar();
        } while (
            !isWS(read.ch)
         && read.ch != SrcReader::CHAR_LINE_END
         && read.ch != SrcReader::CHAR_FILE_END);

        sym.name[len] = '\0';

        debug(Dbg::L0, "number:%s\n", sym.name);

        if (isValidNumberString(sym.name)) {
            sym.type = SYM_LIT_NUMBER;
        }
        else {
            reportError(ERR_INVALID_NUMBER);
        }

    }
    else switch(read.ch)
    {
    case SrcReader::CHAR_FILE_END:
        sym.type = SYM_EOF;
        sym.name[0] = '\0';
        return;
        break;
    case SrcReader::CHAR_LINE_END:
        SINGLE(SYM_EOL, '\0');
        break;
    case '{':
        SINGLE(SYM_BEGIN, '{');
        break;
    case '}':
        SINGLE(SYM_END, '}');
        break;
    case '(':
        SINGLE(SYM_LPAREN, '(');
        break;
    case ')':
        SINGLE(SYM_RPAREN, ')');
        break;
    case '[':
        SINGLE(SYM_LBRACKET, '[');
        break;
    case ']':
        SINGLE(SYM_RBRACKET, ']');
        break;
    case ':':
        SINGLE(SYM_COLON, ':');
        break;
    case '*':
        SINGLE(SYM_STAR, '*');
        break;

    case '=':
        read.nextChar();
        if (read.ch == '=') { // equal "=="
            sym.type = SYM_EQUAL;
            sym.name[0] = '=';
            sym.name[1] = '=';
            sym.name[2] = '\0';
            read.nextChar();
        }
        else {
            sym.type = SYM_ASSIGN;
            sym.name[0] = '=';
            sym.name[1] = '\0';
        }
        break;

    case '/':
        read.nextChar();
        if (read.ch == '/') { // end-of-line comment "//"
            sym.type = SYM_EOL_COMMENT;
            read.until(SrcReader::CHAR_LINE_END);
            read.nextChar();
        }
        else if (read.ch == '*') { // multi line comment "/*"
            sym.type = SYM_MULTI_COMMENT;
            do {
                read.until('*');
                read.nextChar();
            } while (read.ch != '/' && !read.eof() );
            read.nextChar();
        }
        else {
            sym.type = SYM_SLASH;
            sym.name[0] = '/';
            sym.name[1] = '\0';
        }
        break;

    case '"':
        sym.type = SYM_LIT_STRING;
        read.nextChar();
        {
            bool isComplete = false;
            bool isEscape = false;

            while (read.ch != SrcReader::CHAR_LINE_END)
            {
                if (read.ch == '"' && !isEscape) {
                    isComplete = true;
                    break;
                }

                assert(len < Scanner::Symbol::LEXLEN);
                sym.name[len] = read.ch;
                len++;

                isEscape = (read.ch == '\\');

                read.nextChar();
            }

            sym.name[len] = '\0';

            if (!isComplete) {
                reportError(ERR_INCOMPLETE_LIT_STRING);
            }
            else {
                debug(Dbg::L0, "string:%s\n", sym.name);
                read.nextChar();
            }

        }
        break;

    default:
        reportError(ERR_INVALID_SYMBOL);
        read.nextChar();
    }

}

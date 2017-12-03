/**@file
 * @brief     Scanner.
 * @author    Igor Lesik
 * @copyright 2011 Igor Lesik.
 *
 * The main task of the scanner is to provide some way of uniquely identifying
 * each successive token or symbol in the source code.
 *
 */
#include "Scanner.h"

#include <assert.h>

#include "COH.h"
#include "debug.h"

#ifdef NDEBUG
    static inline void debug(uint64_t flags, const char* frmt, ...) {}
#else
    #define debug(flags, frmt, ...)\
        debugModule(DBG_SCAN | flags, "scan", frmt, ##__VA_ARGS__)
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


Keyword keywordList[] = {
    { "package", SYM_K_PACKAGE },
    { "class",   SYM_K_CLASS   },
    /*{ "import",  SYM_K_IMPORT  },
    { "func",    SYM_K_FUNC    },
    { "val",     SYM_K_VAL     },
    { "var",     SYM_K_VAR     },
    { "true",    SYM_K_TRUE    },
    { "false",   SYM_K_FALSE   },*/
};

const char WS[3] = {' ', '\t', '\r'};

void Scanner_create(Scanner* self, SrcReader* srcReader, ErrReport* errReporter)
{
    size_t i;
    const size_t KEYWORDS_NUM = sizeof_array(keywordList);

    self->read = srcReader;
    self->err  = errReporter;

    trie_init(&self->keywords);
    for (i = 0; i < KEYWORDS_NUM; ++i)
    {
        trie_store(&self->keywords, keywordList[i].str, keywordList[i].type);
    }
}

void Scanner_destroy(Scanner* self)
{
    trie_destroy(&self->keywords);
}

inline bool isDigit(char c) {
    return ((c >= '0') && (c <= '9'));
}

inline bool isAlpha(char c) {
    return ((c >= 'A') && (c <= 'Z')) || ((c >= 'a') && (c <= 'z'));
}

inline bool canBeWord1stChar(char c) {
    return isAlpha(c) || c == '_';// || c == '`';
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

bool Scanner_isValidNumberString(const char* s /*, numType*/)
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


void Scanner_getSym(Scanner* self, Symbol* sym)
{
#ifdef NDEBUG
    #define SINGLE(Type,c)\
        sym->type=Type; Scanner_next(self);
#else
    #define SINGLE(Type,c)\
        sym->type=Type; sym->name[0]=c; sym->name[1]='\0'; Scanner_next(self);
#endif

    //debug(Dbg::L2, "get with ch=%c\n", read.ch);

    // Ignore spaces between tokens
    while (isWS(self->read->ch))
        Scanner_next(self);

    int len = 0;

    sym->name[0] = '\0';
    sym->type = SYM_UNKNOWN;

    if (canBeWord1stChar(self->read->ch)) // identifier, type or reserved word
    {
        do { 
            sym->name[len] = self->read->ch;
            len++;
            Scanner_next(self);
        } while(canBeWordChar(self->read->ch));

        sym->name[len] = '\0';

        size_t symType;
        int foundKeyWord = trie_find(&self->keywords, sym->name, &symType);

        if (foundKeyWord) {
            sym->type = (ScanSymType)symType;
        }
        else {
            sym->type = SYM_IDENTIFIER;
        }

        debug(DBG_L_DBG, "%s:%s\n", foundKeyWord? "keyword":"word", sym->name);
    }
    else if (isDigit(self->read->ch))
    {
        do {
            sym->name[len] = self->read->ch;
            len++;
            Scanner_next(self);
        } while (
            !isWS(self->read->ch)
         && self->read->ch != SrcReader_CHAR_LINE_END
         && self->read->ch != SrcReader_CHAR_FILE_END);

        sym->name[len] = '\0';

        debug(DBG_L_DBG, "number:%s\n", sym->name);

        if (Scanner_isValidNumberString(sym->name)) {
            sym->type = SYM_LIT_NUMBER;
        }
        else {
            Scanner_reportError(self, ERR_INVALID_NUMBER);
        }

    }
    else switch(self->read->ch)
    {
    case (int)CHAR_FILE_END:
        sym->type = SYM_EOF;
        sym->name[0] = '\0';
        return;
        break;
    case (int)CHAR_LINE_END:
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
        Scanner_next(self);
        if (self->read->ch == '=') { // equal "=="
            sym->type = SYM_EQUAL;
            sym->name[0] = '=';
            sym->name[1] = '=';
            sym->name[2] = '\0';
            Scanner_next(self);
        }
        else {
            sym->type = SYM_ASSIGN;
            sym->name[0] = '=';
            sym->name[1] = '\0';
        }
        break;

    case '/':
        Scanner_next(self);
        if (self->read->ch == '/') { // end-of-line comment "//"
            sym->type = SYM_EOL_COMMENT;
            SrcReader_until(self->read, SrcReader_CHAR_LINE_END);
            Scanner_next(self);
        }
        else if (self->read->ch == '*') { // multi line comment "/*"
            sym->type = SYM_MULTI_COMMENT;
            do {
                SrcReader_until(self->read, '*');
                Scanner_next(self);
            } while (self->read->ch != '/' && !SrcReader_eof(self->read) );
            Scanner_next(self);
        }
        else {
            sym->type = SYM_SLASH;
            sym->name[0] = '/';
            sym->name[1] = '\0';
        }
        break;

    case '"':
        sym->type = SYM_LIT_STRING;
        Scanner_next(self);
        {
            bool isComplete = false;
            bool isEscape = false;

            while (self->read->ch != SrcReader_CHAR_LINE_END)
            {
                if (self->read->ch == '"' && !isEscape) {
                    isComplete = true;
                    break;
                }

                assert(len < sizeof_array(sym->name));
                sym->name[len] = self->read->ch;
                len++;

                isEscape = (self->read->ch == '\\');

                Scanner_next(self);
            }

            sym->name[len] = '\0';

            if (!isComplete) {
                Scanner_reportError(self, ERR_INCOMPLETE_LIT_STRING);
            }
            else {
                debug(DBG_L_DBG, "string:%s\n", sym->name);
                Scanner_next(self);
            }

        }
        break;

    default:
        Scanner_reportError(self, ERR_INVALID_SYMBOL);
        Scanner_next(self);
    }

}


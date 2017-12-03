/**@file
 * Source reader.
 * Copyright (C) 2011 Igor Lesik.
 *
 */
#include "srcread.h"

#include <assert.h>

#include "defines.h"
#include "debug.h"

#ifdef NDEBUG
    static inline void debug(uint64_t, const char*, ...) {}
#else
    #define debug(flags, frmt, ...)\
        debugModule(Dbg::READ | flags, "read", frmt, ##__VA_ARGS__)
#endif

SrcReader::
SrcReader():
    ch(' '),
    m_curLineNumber(0),
    m_charPos(0),
    m_errorPos(0),
    m_lineLength(0)
{
}

SrcReader::
~SrcReader()
{
}

bool
SrcReader::
open(const char* sourceFileName)
{
    m_srcFile.close();

    if (!m_srcFile.open(sourceFileName, "r")) {
        PRINT("Could not open input file %s, %s\n", sourceFileName,
            Dbg::halo.strerror());
        return false;
    }

    m_lineLength = m_charPos = m_errorPos = 0;

    m_fileName = sourceFileName;

    return true;
}

void
SrcReader::
nextChar()
{
    if (ch == CHAR_FILE_END) return; // input exhausted

    if (isEndLine()) // new line needed
    {
        m_lineLength = m_charPos = m_errorPos = 0;

        m_curLineNumber++;

        onStartNewLine();

        if (NULL == fgets(m_line, LINEMAX, m_srcFile))
        {
            // error or EOF
            m_lineLength = 0;
            m_line[m_lineLength] = CHAR_FILE_END;
        }
        else
        {
            debug(Dbg::L0, "%5d:%s", m_curLineNumber, m_line);

            m_lineLength = strlen(m_line) - 1;
            // mark end with end-of-line and explicit blank space
            m_line[m_lineLength] = CHAR_LINE_END;
            m_line[m_lineLength+1] = ' ';
            m_line[m_lineLength+2] = '\0';
            m_lineLength++;
        }

        m_lineLength++;
    }

    ch = m_line[m_charPos];
    m_charPos++;
}

#undef  DEF_ERROR
#define DEF_ERROR(id, name) name,
static const char* errorString[] = {
    "illegal error code",
    #include "errcode.h"
};
#undef DEF_ERROR

void
SrcReader::
reportError(int errorCode)
{
    if (m_charPos > m_errorPos) // suppress cascading messages
    {
        PRINT("Error in file:%s:%d:%d\n",
            (const char*)m_fileName, m_curLineNumber, m_charPos);

        //onStartNewLine();
        if (m_lineLength > 1) {
            PRINT("%.*s\n", m_lineLength - 2, m_line);
            PRINT("%*c\n", m_charPos, '^');
        }

        assert(ERR__BEGIN < errorCode && errorCode < ERR__END);

        PRINT("Error(%d): %s\n", errorCode, errorString[errorCode]);
    }

    m_errorPos = m_charPos + 1;
}


/**@file
 * @brief     Source reader.
 * @copyright Igor Lesik 2012.
 *
 */
#include "SrcRead.h"

#include <assert.h>

#include "debug.h"

#ifdef NDEBUG
    static inline void debug(uint64_t flags, const char* frmt, ...) {}
#else
    #define debug(flags, frmt, ...) \
        debugModule(DBG_READ | flags, "read", frmt, ##__VA_ARGS__)
#endif

void SrcReader_create(SrcReader* self)
{
    self->ch = ' ';
    File_create(&self->srcFile);
    String_create(&self->fileName, 128, "");
    self->curLineNumber = 0;
    self->charPos = 0;
    self->errorPos = 0;
    self->lineLength = 0;
}

void SrcReader_destroy(SrcReader* self)
{
    File_close(&self->srcFile);
    File_destroy(&self->srcFile);
    String_destroy(&self->fileName);
}

bool
SrcReader_open(SrcReader* self, const char* sourceFileName)
{
    File_close(&self->srcFile);

    if (!File_open(&self->srcFile, sourceFileName, "r"))
    {
        PRINT("Could not open input file %s, %s\n",
            sourceFileName, Dbg_strError());
        return false;
    }

    self->lineLength = self->charPos = self->errorPos = 0;

    //self->fileName = sourceFileName;

    return true;
}

void
SrcReader_nextChar(SrcReader* self)
{
    if (self->ch == SrcReader_CHAR_FILE_END) return; // input exhausted

    if (SrcReader_isEndLine(self)) // new line needed
    {
        self->lineLength = self->charPos = self->errorPos = 0;

        self->curLineNumber++;

        //SrcReader_onStartNewLine(self);

        if (NULL == fgets(self->line, SrcReader_LINEMAX, self->srcFile.fd))
        {
            // error or EOF
            self->lineLength = 0;
            self->line[self->lineLength] = SrcReader_CHAR_FILE_END;
        }
        else
        {
            debug(DBG_L_DBG, "%5d:%s", self->curLineNumber, self->line);

            self->lineLength = strlen(self->line) - 1;
            // mark end with end-of-line and explicit blank space
            self->line[self->lineLength] = SrcReader_CHAR_LINE_END;
            self->line[self->lineLength+1] = ' ';
            self->line[self->lineLength+2] = '\0';
            self->lineLength++;
        }

        self->lineLength++;
    }

    self->ch = self->line[self->charPos];
    self->charPos++;
}

#undef  DEF_ERROR
#define DEF_ERROR(id, name) name,
static const char* errorString[] = {
    "illegal error code",
    #include "errcode.h"
};
#undef DEF_ERROR

void
SrcReader_reportError(SrcReader* self, int errorCode)
{
    if (self->charPos > self->errorPos) // suppress cascading messages
    {
        PRINT("Error in file:%s:%d:%d\n",
            self->fileName.p, self->curLineNumber, self->charPos);

        //onStartNewLine();
        if (self->lineLength > 1) {
            PRINT("%.*s\n", self->lineLength - 2, self->line);
            PRINT("%*c\n", self->charPos, '^');
        }

        assert(ERR__BEGIN < errorCode && errorCode < ERR__END);

        PRINT("Error(%d): %s\n", errorCode, errorString[errorCode]);
    }

    self->errorPos = self->charPos + 1;
}


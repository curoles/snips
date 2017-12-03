/**@file
 * @brief     Source reader.
 * @copyright Igor Lesik 2012.
 *
 */
#pragma once
#ifndef COH_SRCREAD_H_INCLUDED
#define COH_SRCREAD_H_INCLUDED

#include "stddef.h"

#include "File.h"
#include "String.h"

#define CHAR_FILE_END  '\0'
#define CHAR_LINE_END  '\4'
static const char SrcReader_CHAR_FILE_END = '\0';
static const char SrcReader_CHAR_LINE_END = '\4';

enum { SrcReader_LINEMAX = 256 };

/** File handling routine that has the task of transmitting the source
 *  character by character to the scanner or lexical analyser.
 *
 * Scanner will assemble transmitted characters into tokens/symbols.
 */
struct SrcReader
{
    char ch; // latest character read

    File srcFile;      // Source file
    String fileName;   // Input file name
    int curLineNumber; // Current line number
    int charPos;       // Character pointer
    int errorPos;      // Last error position
    int lineLength;    // Line length

    char line[SrcReader_LINEMAX + 3]; // Last line read
};

typedef struct SrcReader SrcReader;

void SrcReader_create(SrcReader*);
void SrcReader_destroy(SrcReader*);

static inline
bool SrcReader_eof(SrcReader* self)
{
	return self->ch == SrcReader_CHAR_FILE_END;
}

// Returns true when end of current line has been reached.
static inline
bool SrcReader_isEndLine(SrcReader* self)
{
	return (self->charPos == self->lineLength);
}

// ch is returned as CHAR_FILE_END if src is exhausted.
void SrcReader_nextChar(SrcReader* self);

static inline
void SrcReader_until(SrcReader* self, char c)
{
    do { SrcReader_nextChar(self); }
    while (self->ch != c && !SrcReader_eof(self));
}

// Points out error identified by errorcode with suitable message
void SrcReader_reportError(SrcReader* self, int errorCode);

// Called at start of each line.
//static inline
//void onStartNewLine() {}

bool SrcReader_open(SrcReader* self, const char* sourceFileName);


#endif

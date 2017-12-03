/**@file
 * Source reader.
 * Copyright (C) 2011 Igor Lesik.
 *
 */
#pragma once
#ifndef HALO_SRCREAD_H_INCLUDED
#define HALO_SRCREAD_H_INCLUDED

#include "file.h"
#include "ztring.h"

/** File handling routine that has the task of transmitting the source
 *  character by character to the scanner or lexical analyser.
 *
 * Scanner will assemble transmitted characters into tokens/symbols.
 */
class SrcReader
{
public:
    static const char CHAR_FILE_END = '\0';
    static const char CHAR_LINE_END = '\4';

    enum { LINEMAX = 256 };

public:
    char ch; // latest character read

    // ch is returned as NUL if src is exhausted.
    void nextChar();

    // Returns true when end of current line has been reached.
    bool isEndLine() { return (m_charPos == m_lineLength); }
    
    // Points out error identified by errorcode with suitable message
    void reportError(int errorCode);

    // Called at start of each line.
    /*virtual*/ void onStartNewLine() {;}

    // Returns current line number.
    int getCurLineNumber() { return m_curLineNumber; }

    bool open(const char* sourceFileName);

    void until(char c) { 
        do { nextChar(); }
        while (ch != c && !eof());
    }

    inline bool eof() { return ch == CHAR_FILE_END; }

    SrcReader();

   ~SrcReader();

private:
    File m_srcFile; // Source file
    string m_fileName;
    int m_curLineNumber; // Current line number
    int m_charPos; // Character pointer
    int m_errorPos; // Last error position
    int m_lineLength; // Line length

    char m_line[LINEMAX + 3]; // Last line read
};


#endif

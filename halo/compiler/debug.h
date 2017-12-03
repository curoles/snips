/**@file
 * Debug print.
 * Copyright (C) 2011 Igor Lesik.
 *
 */
#pragma once
#ifndef HALO_DEBUG_H_INCLUDED
#define HALO_DEBUG_H_INCLUDED

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>

/// Print out compiler messages.
#define PRINT(frmt, ...) fprintf(stdout, frmt, ##__VA_ARGS__)

class Dbg
{
public:
    // Debug levels:
    static const uint64_t L0         = 0x0ull;
    static const uint64_t L1         = 0x1ull;
    static const uint64_t L2         = 0x2ull;
    
    // Debug components and functions:
    static const uint64_t ALL      = ~0x0Full;
    static const uint64_t ALWAYS   = (1ull << 63);
    static const uint64_t INIT     = 0x000000010ull;
    static const uint64_t READ     = 0x000000020ull;
    static const uint64_t SCAN     = 0x000000040ull;
    static const uint64_t PARSE    = 0x000000080ull;
    static const uint64_t AST      = 0x000000100ull;
    static const uint64_t CODEGEN  = 0x000000200ull;

public:
#ifdef NDEBUG
    void print(uint64_t flags, const char* frmt, ...) {}
#else
    void print(uint64_t flags, const char* frmt, ...);
#endif

    void  setStream(FILE* stream){ m_stream = stream; }
    FILE* getStream(){ return m_stream; }

    void     setFlags(uint64_t flags){ m_flags = flags; }
    void     addFlags(uint64_t flags){ m_flags |= flags; }
    uint64_t getFlags(){ return m_flags; }

    char* strerror();

    Dbg(FILE* stream   = stderr,
        uint64_t level = L2,
        uint64_t flags = ALWAYS);

private:
    FILE*    m_stream;
    uint64_t m_level;
    uint64_t m_flags;
    char     m_strerror[512];

public:
    static Dbg halo;
    //static Dbg parser;
};


#define debugModule(flags, module, frmt, ...)\
    Dbg::halo.print(flags, "%-8s: "frmt, module, ##__VA_ARGS__)


#define debugHalo(flags, frmt, ...)\
    debugModule(flags, "halo", frmt, ##__VA_ARGS__)

#if 0
/** This class implements FILE stream inerface to allow output text manipulations.
 *
 *
 */
class CustomDbgStream
{

public:
    CustomDbgStream(const char* name, uint64_t stream_id);
   ~CustomDbgStream();

    FILE* getFILE() { return fp; }

    //static ssize_t stream_read(void* c, char* buf, size_t size);
    static ssize_t stream_write(void* c, const char* buf, size_t size);
    static int stream_close(void* c);

    static cookie_io_functions_t stream_func;

private:
    typedef struct stream_cookie {
        CustomDbgStream* stream;
        const char*      name;
        uint64_t         stream_id;
        char             buf[1024];
    } stream_cookie_t;

    stream_cookie_t cookie;

    FILE* fp;
};
#endif

#endif

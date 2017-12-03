/**@file
 * @brief     Debug print.
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012.
 *
 */
#pragma once
#ifndef COH_DEBUG_H_INCLUDED
#define COH_DEBUG_H_INCLUDED

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>

extern FILE* LOG;

/// Print out compiler messages.
#define PRINT(frmt, ...) fprintf(LOG, frmt, ##__VA_ARGS__)

// Debug levels:
#define DBG_L0   0x0ull
#define DBG_L1   0x1ull
#define DBG_L2   0x2ull
#define DBG_L3   0x3ull
#define DBG_L4   0x4ull

static const uint64_t DBG_L_NOISY    = DBG_L4;
static const uint64_t DBG_L_DBG      = DBG_L3;
static const uint64_t DBG_L_INFO     = DBG_L2;
static const uint64_t DBG_L_WARN     = DBG_L1;
static const uint64_t DBG_L_ERR      = DBG_L0;

// Debug components and functions:
static const uint64_t DBG_NONE     = 0x00000000Full;
static const uint64_t DBG_ALL      =~0x00000000Full;
static const uint64_t DBG_ALWAYS   = (1ull << 63);
static const uint64_t DBG_INIT     = 0x000000010ull;
static const uint64_t DBG_READ     = 0x000000020ull;
static const uint64_t DBG_SCAN     = 0x000000040ull;
static const uint64_t DBG_PARSE    = 0x000000080ull;
static const uint64_t DBG_AST      = 0x000000100ull;
static const uint64_t DBG_CODEGEN  = 0x000000200ull;
static const uint64_t DBG_COMPILE  = 0x000000400ull;


#ifdef NDEBUG
    static inline void Dbg_print(uint64_t flags, const char* frmt, ...) {}
#else
    void Dbg_print(uint64_t flags, const char* frmt, ...);
#endif

extern FILE*    Dbg_stream;
extern uint64_t Dbg_flags;
extern uint64_t Dbg_level;
extern char     Dbg_strerror[512];

static inline
void  Dbg_setStream(FILE* stream) { Dbg_stream = stream; }

static inline
void Dbg_configure(FILE* stream, uint64_t level, uint64_t flags)
{
	Dbg_stream = stream;
	Dbg_level  = level;
	Dbg_flags  = flags;
}

static inline
uint64_t Dbg_addFlags(uint64_t flags)
{
	Dbg_flags |= flags;
	return Dbg_flags;
}

char* Dbg_strError();

#define debugModule(flags, module, frmt, ...) \
    Dbg_print(flags, "%-8s: "frmt, module, ##__VA_ARGS__)

#define debugCoh(flags, frmt, ...) \
    debugModule(flags, "coH", frmt, ##__VA_ARGS__)


#endif

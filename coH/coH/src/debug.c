/**@file
 * @brief     Debug print.
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012.
 *
 */
#include "debug.h"

#include <stdio.h>
#include <stdarg.h>
#include <errno.h>

#include "COH.h"

FILE* LOG = NULL;

FILE*    Dbg_stream = NULL;
uint64_t Dbg_flags = ~0x0Full;
uint64_t Dbg_level = DBG_L4;
char     Dbg_strerror[512] = {0};


#ifndef NDEBUG
void Dbg_print(uint64_t flags, const char* frmt, ...)
{
    if (!(flags & Dbg_flags) || ((flags & 0xF) > Dbg_level))
        return;

    //lock();

    va_list ap;
    va_start(ap, frmt);
    vfprintf(Dbg_stream, frmt, ap);
    va_end(ap);

    //unlock();
}
#endif

char*
Dbg_strError()
{
    if (0 != strerror_r(errno, Dbg_strerror, sizeof_array(Dbg_strerror)))
    {
        Dbg_strerror[0] = '\0';
    }

    return Dbg_strerror;
}



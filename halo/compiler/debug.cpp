/**@file
 * Debug print.
 * Copyright (C) 2011 Igor Lesik.
 *
 */
#include "debug.h"

#include <stdio.h>
#include <stdarg.h>
#include <errno.h>

#include "defines.h"

Dbg Dbg::halo;
 
Dbg::
Dbg(FILE* stream, uint64_t level, uint64_t flags):
    m_stream(stream), m_level(level), m_flags(flags)
{
}

#ifndef NDEBUG
void
Dbg::
print(uint64_t flags, const char* frmt, ...)
{
    if (!(flags & m_flags) || ((flags & 0xF) > m_level))
        return;

     //lock();

    va_list ap;
    va_start(ap, frmt);
    vfprintf(m_stream, frmt, ap);
    va_end(ap);

    //unlock();
}
#endif

char*
Dbg::
strerror()
{
    if (0 != strerror_r(errno, m_strerror, sizeof_array(m_strerror))) {
        m_strerror[0] = '\0';
    }

    return m_strerror;
}



#if 0
CustomDbgStream::
CustomDbgStream(const char* name, uint64_t stream_id):
    fp(NULL)
{
    cookie.stream = this;
    cookie.name = name;
    cookie.stream_id = stream_id;
    cookie.buf[0] = '\0';

    fp = fopencookie(&cookie, "w", stream_func);
}

CustomDbgStream::
~CustomDbgStream()
{
    if (fp)
        fclose(fp);
}

cookie_io_functions_t CustomDbgStream::stream_func = {
    /*.read  =*/ NULL,
    /*.write =*/ CustomDbgStream::stream_write,
    /*.seek  =*/ NULL,
    /*.close =*/ CustomDbgStream::stream_close
};

ssize_t
CustomDbgStream::
stream_write(void* c, const char* buf, size_t size)
{
    if (!c)
        return -1;

    stream_cookie* This = (stream_cookie*)c;

    if (!This->stream)
        return -1;

    size_t i = 0, pos = strlen(This->buf);

    for (; i < size; i++, pos++ )
    {
        if (buf[i] == '\n' || pos == (sizeof_array(This->buf) - 1)) {
            Dbg::halo.print(
                Dbg::ALWAYS,
                "%13s %u | %.*s",
                This->name,
                This->stream_id,
                pos,
                This->buf
            );

            This->buf[0] = '\0';
            break;
        }
        else {
            This->buf[pos] = buf[i];
        }
    }

    This->buf[pos]='\0';
 

    return i;
}

int
CustomDbgStream::
stream_close(void* c)
{
    stream_cookie* This = (stream_cookie*)c;
    This->stream = NULL;

    return 0;
}
#endif

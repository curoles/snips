/**@file
 * Common definitions.
 * Copyright (C) 2011 Igor Lesik.
 *
 */
#pragma once
#ifndef HALO_DEFINES_H_INCLUDED
#define HALO_DEFINES_H_INCLUDED

#include <stdint.h>
#include <string.h>

template<class T> size_t sizeof_array(const T& array)
{
    return sizeof(array)/sizeof(array[0]);
}

#undef  DEF_ERROR
#define DEF_ERROR(id, name) ERR_##id,
enum {
    ERR__BEGIN=0,
    #include "errcode.h"
    ERR__END,
};
#undef  DEF_ERROR

#endif

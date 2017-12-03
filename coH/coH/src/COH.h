/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012
 *
 */
#pragma once
#ifndef COH_H_INCLUDED
#define COH_H_INCLUDED

#include <stdint.h>
#include <stdio.h>

typedef int32_t error_t;

#undef  DEF_ERROR
#define DEF_ERROR(id, name) ERR_##id,
enum Error {
    ERR__BEGIN=0,
    #include "errcode.h"
    ERR__END,
};
#undef  DEF_ERROR

#define sizeof_array(array) (sizeof(array)/sizeof(array[0]))


#define STR_CONCAT(a,b) a##b

#define BEGIN_UNIT_TEST(name,id)                    \
__attribute__ ((constructor(101+id)))               \
static void STR_CONCAT(name##_unit_test_,id) () {   \
__builtin_printf("Unit test:%s...", __FUNCTION__);


#define END_UNIT_TEST \
__builtin_puts("PASSED"); }

#endif //  COH__H_INCLUDED

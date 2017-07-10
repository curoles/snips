/**@file
 * @brief     Custom string allocation
 * @author    Igor Lesik 2017
 * @copyright Igor Lesik 2017
 *
 *
 *
 */
#pragma once

#ifndef IGR_STRING_H_INCLUDED
#define IGR_STRING_H_INCLUDED

#include "igr.h"

/** Store input string in permanently allocated memory space. 
 *  @param s input string
 *  @return pointer to permanently stored copy of input string
 */
char* string(char* s);

/** Store input string in permanently allocated memory space. 
 *  @param s input string
 *  @param length of input string, \0 included
 *  @return pointer to permanently stored copy of input string
 */
char* stringL(char* s, uint lenght);

char* stringd(int val);

void show_string_hash_distribution(uint chunk);

#endif /*IGR_STRING_H_INCLUDED*/

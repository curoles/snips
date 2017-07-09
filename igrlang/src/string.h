#pragma once

#ifndef IGR_STRING_H_INCLUDED
#define IGR_STRING_H_INCLUDED

#include "igr.h"

char* string(char* s);
char* stringL(char* s, uint len);
char* stringd(int val);

void show_string_hash_distribution(uint chunk);

#endif /*IGR_STRING_H_INCLUDED*/

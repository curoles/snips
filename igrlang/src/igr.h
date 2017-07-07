#pragma once

#ifndef IGR_H_INCLUDED
#define IGR_H_INCLUDED

typedef unsigned int uint;
typedef unsigned long ulong;
typedef char byte;

//typedef unsigned char bool;
typedef
enum bool {true = 1, false = 0}
bool;

#ifndef NULL
#define NULL ( (void *) 0)
#endif

#define sizeof_array(a) ((sizeof(a))/(sizeof(a[0])))

enum RetStatus {SUCCESS=0, FAIL=1};

#endif /*IGR_H_INCLUDED*/

//http://howtowriteaprogram.blogspot.com/2010/11/lisp-interpreter-in-90-lines-of-c.html

#pragma once
#ifndef LISP_PRIMITIVES_H_INCLUDED
#define LISP_PRIMITIVES_H_INCLUDED

#include "env.h"

namespace ulisp {

void add_globals(Environment& env);

}

#endif

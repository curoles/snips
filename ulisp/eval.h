//http://howtowriteaprogram.blogspot.com/2010/11/lisp-interpreter-in-90-lines-of-c.html

#pragma once
#ifndef LISP_EVAL_H_INCLUDED
#define LISP_EVAL_H_INCLUDED

#include <string>

namespace ulisp {

struct Cell;
class CellFactory;
struct Environment;

const Cell* eval(CellFactory& factory, const Cell& root, Environment& env);

const Cell* eval(CellFactory& factory, const char* x);

}

#endif

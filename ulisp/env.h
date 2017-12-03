//http://howtowriteaprogram.blogspot.com/2010/11/lisp-interpreter-in-90-lines-of-c.html

#pragma once
#ifndef LISP_ENV_H_INCLUDED
#define LISP_ENV_H_INCLUDED
 
//#include <string>
//#include <vector>
//#include <map>

#include <iostream>
#include <cstdlib>

#include "cell.h"

namespace ulisp {

// a dictionary that (a) associates symbols with cells, and
// (b) can chain to an "outer" dictionary
struct Environment
{
    Environment(Environment* outer = NULL) : m_outer(outer) {}

    /*Environment(const Cells& parms, const Cells& args, Environment* outer)
    : m_outer(outer)
    {
        CellsIt a = args.begin();
        for (CellsIt p = parms.begin(); p != parms.end(); ++p)
            m_env[p->val] = *a++;
    }*/

    // map a variable name onto a cell
    typedef std::map<std::string, Cell> Map;

    // return a reference to the innermost environment where 'var' appears
    Map& find(const std::string& var)
    {
        if (m_env.find(var) != m_env.end())
            return m_env; // the symbol exists in this environment
        if (m_outer)
            return m_outer->find(var); // attempt to find the symbol in some "outer" env
        std::cout << "unbound symbol '" << var << "'\n";
        exit(1);
    }

    // return a reference to the cell associated with the given symbol 'var'
    Cell& operator[] (const std::string& var)
    {
        return m_env[var];
    }
    
private:
    Map m_env; // inner symbol->cell mapping
    Environment* m_outer; // next adjacent outer env, or 0 if there are no further environments
};

}

#endif

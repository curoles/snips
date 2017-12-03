//http://howtowriteaprogram.blogspot.com/2010/11/lisp-interpreter-in-90-lines-of-c.html

#pragma once
#ifndef LISP_CELL_H_INCLUDED
#define LISP_CELL_H_INCLUDED
 
#include <string>
#include <vector>
#include <map>
#include <list>

namespace ulisp {

struct Environment;

class CellFactory;

// a variant that can hold any kind of lisp value
//
struct Cell
{
    typedef std::vector<const Cell*> List;
    typedef Cell* (*ProcType)(CellFactory&, const List&);

    typedef List::const_iterator Iter;
    //typedef std::map<std::string, Cell> Map;

    #define SYM__TYPE(name) T_##name
    enum CellType {
    #include "symtype.h"
    };
    #undef SYM__TYPE
    CellType type;

    std::string val;
    List list;
    ProcType proc;
    Environment* env;

    Cell(CellType type = T_SYMBOL) : type(type), env(NULL) {}
    Cell(CellType type, const std::string& val) : type(type), val(val), env(NULL) {}
    Cell(ProcType proc) : type(T_PROC), proc(proc), env(NULL) {}

    static const Cell false_sym;// (Symbol, "#f");
    static const Cell true_sym;//(Symbol, "#t"); // anything that isn't false_sym is true
    static const Cell nil;//(Symbol, "nil");

    // convert given cell to a Lisp-readable string
    std::string to_string() const;

    void parse(CellFactory& factory, const char* input);
    void read(CellFactory& factory, std::list<std::string>& tokens);
    void construct_atom(const std::string& token);

    static
    const char* type2str(CellType type);

};

typedef Cell::List Cells;
typedef Cells::const_iterator CellsIt;

class CellFactory
{
private:
    typedef std::vector<Cell> Storage;
    Storage m_storage;

public:
    Cell& make(Cell::CellType type = Cell::T_SYMBOL) {
        m_storage.push_back(Cell(type));
        return m_storage.back();
    }

    Cell& make(Cell::CellType type, const std::string& val) {
        m_storage.push_back(Cell(type, val));
        return m_storage.back();
    }

};

}

#endif

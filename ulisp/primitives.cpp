/**
 * @brief built-in primitive procedures
 */
#include "primitives.h"

#include <sstream>
#include <cstdlib>

#include "cell.h"

using namespace ulisp;

// return given mumber as a string
std::string num2str(long n) { std::ostringstream os; os << n; return os.str(); }

Cell* proc_add(CellFactory& factory, const Cells& c)
{
    long n(atol(c[0]->val.c_str()));

    for (CellsIt i = c.begin()+1; i != c.end(); ++i)
    {
        n += atol((*i)->val.c_str());
    }

    return &factory.make(Cell::T_NUMBER, num2str(n));
}

#if 0
cell proc_sub(const cells & c)
{
    long n(atol(c[0].val.c_str()));
    for (cellit i = c.begin()+1; i != c.end(); ++i) n -= atol(i->val.c_str());
    return cell(Number, str(n));
}

cell proc_mul(const cells & c)
{
    long n(1);
    for (cellit i = c.begin(); i != c.end(); ++i) n *= atol(i->val.c_str());
    return cell(Number, str(n));
}

cell proc_div(const cells & c)
{
    long n(atol(c[0].val.c_str()));
    for (cellit i = c.begin()+1; i != c.end(); ++i) n /= atol(i->val.c_str());
    return cell(Number, str(n));
}

cell proc_greater(const cells & c)
{
    long n(atol(c[0].val.c_str()));
    for (cellit i = c.begin()+1; i != c.end(); ++i)
        if (n <= atol(i->val.c_str()))
            return false_sym;
    return true_sym;
}

cell proc_less(const cells & c)
{
    long n(atol(c[0].val.c_str()));
    for (cellit i = c.begin()+1; i != c.end(); ++i)
        if (n >= atol(i->val.c_str()))
            return false_sym;
    return true_sym;
}

cell proc_less_equal#include <string>
#include <vector>
#include <map>

struct Environment;

// a variant that can hold any kind of lisp value
//
struct Cell
{
    typedef Cell (*ProcType)(const std::vector<Cell> &);

    typedef std::vector<Cell>::const_iterator iter;
    typedef std::map<std::string, Cell> map;

    enum CellType { Symbol, Number, List, Proc, Lambda };
    CellType type;

    std::string val;
    std::vector<Cell> list;
    ProcType proc;
    Environment* env;

    Cell(CellType type = Symbol) : type(type), env(NULL) {}
    Cell(CellType type, const std::string & val) : type(type), val(val), env(NULL) {}
    Cell(ProcType proc) : type(Proc), proc(proc), env(NULL) {}

    static const Cell false_sym;// (Symbol, "#f");
    static const Cell true_sym;//(Symbol, "#t"); // anything that isn't false_sym is true
    static const Cell nil;//(Symbol, "nil");

};

typedef std::vector<Cell> Cells;
typedef Cells::const_iterator CellsIt;
(const cells & c)
{
    long n(atol(c[0].val.c_str()));
    for (cellit i = c.begin()+1; i != c.end(); ++i)
        if (n > atol(i->val.c_str()))
            return false_sym;
    return true_sym;
}

cell proc_length(const cells & c) { return cell(Number, str(c[0].list.size())); }
cell proc_nullp(const cells & c)  { return c[0].list.empty() ? true_sym : false_sym; }
cell proc_car(const cells & c)    { return c[0].list[0]; }

cell proc_cdr(const cells & c)
{
    if (c[0].list.size() < 2)
        return nil;
    cell result(c[0]);
    result.list.erase(result.list.begin());
    return result;
}

cell proc_append(const cells & c)
{
    cell result(List);
    result.list = c[0].list;
    for (cellit i = c[1].list.begin(); i != c[1].list.end(); ++i) result.list.push_back(*i);
    return result;
}

cell proc_cons(const cells & c)
{
    cell result(List);
    result.list.push_back(c[0]);
    for (cellit i = c[1].list.begin(); i != c[1].list.end(); ++i) result.list.push_back(*i);
    return result;
}

cell proc_list(const cells & c)
{
    cell result(List); result.list = c;
    return result;
}

#endif

// define basic primintives
//
void ulisp::add_globals(Environment& env)
{
    env["nil"] = Cell::nil;
    env["#f"]  = Cell::false_sym;
    env["#t"]  = Cell::true_sym;

    //env["append"] = cell(&proc_append);
    //env["car"]    = cell(&proc_car);
    //env["cdr"]    = cell(&proc_cdr);
    //env["cons"]   = cell(&proc_cons);
    //env["length"] = cell(&proc_length);
    //env["list"]   = cell(&proc_list);
    //env["null?"]  = cell(&proc_nullp);
    env["+"]      = Cell(&proc_add);
    //env["-"]      = cell(&proc_sub);
    //env["*"]      = cell(&proc_mul);
    //env["/"]      = cell(&proc_div);
    //env[">"]      = cell(&proc_greater);
    //env["<"]      = cell(&proc_less);
    //env["<="]     = cell(&proc_less_equal);
}


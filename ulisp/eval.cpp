#include "eval.h"

#include <cstdio>
#include <cassert>

#include "cell.h"
#include "env.h"
#include "primitives.h"

#define DEBUG_EVAL
#ifdef  DEBUG_EVAL
#define DBG(frmt, ...) printf("eval: "frmt, ## __VA_ARGS__)
#else
#define DBG(frmt, ...) do{}while(0)
#endif


using namespace ulisp;

static ulisp::Environment global_env;
namespace {struct X{X(){ulisp::add_globals(global_env);}};}

const Cell* ulisp::eval(CellFactory& factory, const char* x)
{
    Cell& root = factory.make();
    root.parse(factory, x);

    return ulisp::eval(factory, root, global_env);
}


const Cell* ulisp::eval(CellFactory& factory, const Cell& x, Environment& env)
{

    if (x.type == Cell::T_SYMBOL)
    {
        return &env.find(x.val)[x.val];
    }
/*
    if (x.type == Cell::Number)
        return x;
*/
    if (x.list.empty())
        return &Cell::nil;

    assert(x.type == Cell::T_LIST);

    if (x.list[0]->type == Cell::T_SYMBOL)
    {
        DBG("list[0] is '%s'\n", x.list[0]->val.c_str());

        if (x.list[0]->val == "quote") // (quote exp)
        {
            return x.list[1];
        }
#if 0
        if (x.list[0].val == "if")          // (if test conseq [alt])
            return eval(eval(x.list[1], env).val == "#f" ? (x.list.size() < 4 ? Cell::nil : x.list[3]) : x.list[2], env);
        if (x.list[0].val == "set!")        // (set! var exp)
            return env->find(x.list[1].val)[x.list[1].val] = eval(x.list[2], env);
        if (x.list[0].val == "define")      // (define var exp)
            return (*env)[x.list[1].val] = eval(x.list[2], env);
        if (x.list[0].val == "lambda") {    // (lambda (var*) exp)
            x.type = Lambda;
            // keep a reference to the environment that exists now (when the
            // lambda is being defined) because that's the outer environment
            // we'll need to use when the lambda is executed
            x.env = env;
            return x;
        }
        if (x.list[0].val == "begin") {     // (begin exp*)
            for (size_t i = 1; i < x.list.size() - 1; ++i)
                eval(x.list[i], env);
            return eval(x.list[x.list.size() - 1], env);
        }
#endif
    }


    // (proc exp*)
    const Cell* func = eval(factory, *x.list[0], env);

    //cell proc(eval(x.list[0], env));
    Cells exps;
    for (CellsIt exp = x.list.begin() + 1; exp != x.list.end(); ++exp)
    {
        const Cell* operand = eval(factory, **exp, env);
        exps.push_back(operand);
    }

    if (func->type == Cell::T_LAMBDA) {
        // Create an environment for the execution of this lambda function
        // where the outer environment is the one that existed* at the time
        // the lambda was defined and the new inner associations are the
        // parameter names with the given arguments.
        // *Although the environmet existed at the time the lambda was defined
        // it wasn't necessarily complete - it may have subsequently had
        // more symbols defined in that environment.
#if 0
        return eval(
            /*body*/proc.list[2],
            new environment(/*parms*/proc.list[1].list,
            /*args*/exps, proc.env)
        );
#endif
return NULL;
    }
    else if (func->type == Cell::T_PROC)
    {
        return func->proc(factory, exps);
    }

    DBG("Error: not a function\n");

    DBG("Error: could not evaluate %s\n", Cell::type2str(x.type));

    return NULL;
}



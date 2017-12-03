#include <cstdlib>
#include <cstdio>

#include "eval.h"
#include "cell.h"

int test(const char* exp, const char* expect)
{
    ulisp::CellFactory factory;
    const ulisp::Cell* res = NULL;

    res = ulisp::eval(factory, exp);

    if (!res)
    {
        printf("ulisp::eval failed\n");
        return 1;
    }

    std::string s = res->to_string();

    if (s != expect)
    {
        printf("uLisp error:\n%s\nvs.\n%s\n", s.c_str(), expect);
        return 1;
    }

    return 0;
}

#define TEST(x,e) int main() { return test(x, e); }

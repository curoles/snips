#include <string>
#include <iostream>
#include <cstdlib>

static int g_stop_request = 0;

void sighandler(int sig)
{
    g_stop_request = sig;
    std::cout<< "*** SIGNAL" << std::endl;
}

// the default read-eval-print-loop
void repl(const std::string& prompt/*, Environment* env*/)
{
    while (!g_stop_request)
    {
        std::cout << prompt;
        std::string line;
        std::getline(std::cin, line);
        //std::cout << to_string(eval(read(line), env)) << '\n';
    }
}

#include <signal.h>
//#include "primitives.h"
//#include "env.h"

int main(int argc, char** argv)
{
    signal(SIGABRT, &sighandler);
    signal(SIGTERM, &sighandler);
    signal(SIGINT,  &sighandler);

    //ulisp::Environment global_env;
    //ulisp::add_globals(global_env);
    repl("lisp> "/*, &global_env*/);

    return EXIT_SUCCESS;
}

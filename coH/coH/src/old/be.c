#include <stdlib.h>

#include "debug.h"
#include "defClass.h"
#include "defFun.h"
#include "File.h"
#include "ir.h"

error_t run(FILE* out)
{
    IrClass classA;
    IrClassMemberVar var_a;
    IrClassMemberVar var_b;
    IrClassMemberVar_create(&var_a, "a", "int");
    IrClassMemberVar_create(&var_b, "b", "char");

    IrClass_create(&classA, "ClassA");
    classA.vars = List_push_front(classA.vars, &var_a);
    classA.vars = List_push_front(classA.vars, &var_b);

    defClass(out, 0, &classA);

    IrClass_destroy(&classA);

    IrClassMemberVar_destroy(&var_a);
    IrClassMemberVar_destroy(&var_b);

    IrFunction fun1;
    IrFunction_create(&fun1, "fun1");
    defFun(out,0,&fun1);
    IrFunction_destroy(&fun1);

    fprintf(out, "void main(){}\n");

    return ERR_OK;
}


int run_bc()
{

    withFile(LOG, "test.c", "w", run);

    return 0;
}

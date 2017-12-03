/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012
 *
 */
#include "be.h"

#include "ast.h"

//#include "defVarMember.h"

void 
be_defClass(
    FILE* out,
    size_t indent,
    AST* ast
)
{
    assert(ast);

    const char* class_name = ast->token.str.p;

    LN("struct %s\n", class_name);
    LN("{\n");
    /*{
    List vars = ir->vars;
    ++indent;
    for (; vars; vars = vars->rest)
    {
        IrClassMemberVar* var = (IrClassMemberVar*)vars->first_el;
        defVarMember(out, indent, var);
    }
    --indent;
    }*/
    LN("};\n");
    LN("typedef struct %s %s;\n\n", class_name, class_name);
}


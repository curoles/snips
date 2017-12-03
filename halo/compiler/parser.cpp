/**@file
 * LL(1) Parser for syntax analysis.
 * Copyright (C) 2011 Igor Lesik.
 *
 */
#include "parser.h"

#include "defines.h"
#include "srcread.h"
#include "ast.h"
#include "erreport.h"
#include "debug.h"

#ifdef NDEBUG
    static inline void debug(uint64_t, const char*, ...) {}
#else
    #define debug(flags, frmt, ...)\
        debugModule(Dbg::PARSE | flags, "parse", frmt, ##__VA_ARGS__)
#endif

Parser::Parser(SrcReader& sr, ErrReport& er, Scanner& scanner):
    m_srcReader(sr),
    m_errReport(er),
    m_scanner(scanner)
{
}

Parser::~Parser()
{
}

bool Parser::accept(ScanSymType type, int errCode, bool skip_eol, bool consume)
{
    //if (isDone())
    //    return false;

    // Skip comments.
    while (sym.type != type && isSkippableType(sym.type)) {
        if (!skip_eol && (sym.type == SYM_EOL || sym.type == SYM_EOL_COMMENT))
            break;
        debug(Dbg::L2, "symbol(%-8s):%s\n", symName(sym.type), sym.name);
        getSym();
    }

    if (sym.type == type) {
        debug(Dbg::L2, "symbol(%-8s):%s\n", symName(sym.type), sym.name);
        if (consume) getSym();
        return true;
    }
    else {
        reportError(errCode);
        return false;
    }
}

bool Parser::lookFor(ScanSymType types[], size_t size, ScanSymType& foundType)
{
    foundType = SYM__ILLEGAL;

    // Skip comments.
    while (isSkippableType(sym.type)) {
        debug(Dbg::L2, "symbol(%-8s):%s\n", symName(sym.type), sym.name);
        getSym();
    }

    foundType = sym.type;

    for (size_t i = 0; i < size; ++i) {
        if (sym.type == types[i]) {
            debug(Dbg::L2, "found expected symbol %s:%s\n",
                symName(sym.type), sym.name);
            return true;
        }
    }

    return false;
}

void Parser::reportUnexpectedSymError(
    ScanSymType type,
    ScanSymType expectedTypes[],
    size_t size)
{
    reportError(ERR_UNEXPECTED_SYMBOL);

    PRINT("Error: unexpected symbol %s, expected:", symName(type));

    for (size_t i = 0; i < size; ++i) {
        assert(i < SYM__END);
        PRINT(" %s,", symName(expectedTypes[i]));
    }

    PRINT("\n");
}

void Parser::parse(AST& ast)
{
    sym.type = SYM_EOF;

    // kick off Reader, read 1st character 
    m_srcReader.nextChar();

    // kick off Scanner, get 1st symbol
    getSym();

    parse_TopPackage(&ast);
}

/**
 *  TopPackage =
 *      "package" PackageId EOL PackageBody
 *  ;
 *
 */
void Parser::parse_TopPackage(AST* root_ast)
{
    if (accept(SYM_K_PACKAGE, ERR_KW_PACKAGE_EXPECTED) )
    {
        if (accept(SYM_IDENTIFIER, ERR_IDENTIFIER_EXPECTED, !SKIP_EOL, !CONSUME) )
        {
            AST* ast = new AST(AST::Token::TOKEN_PKG, sym.name);
            root_ast->addChild(ast);
            getSym();

            if (accept(SYM_EOL, ERR_EOL_EXPECTED) )
            {
                while (!isDone()) {
                    parse_PackageBody(ast); 
                }
            }
        }
    }
}

/**
 *  PackageBody =
 *      ImportStatement
 *    | NestedPackage
 *    | FuncDeclaration
 *    | ValDeclaration
 *  ;
 */
void Parser::parse_PackageBody(AST* root_ast)
{
    ScanSymType types[] = {
        SYM_K_IMPORT,
        SYM_K_PACKAGE,
        SYM_K_FUNC,
        SYM_K_VAL,
    };

    ScanSymType foundType = SYM__ILLEGAL;
    bool found = lookFor(types, sizeof_array(types), foundType);

    if (!found && !isDone()) {
        reportUnexpectedSymError(foundType, types, sizeof_array(types));
        return;
    }

    debug(Dbg::L0, "found type %s\n", symName(foundType));

    switch (foundType) {
    case SYM_K_VAL:
        parse_ValDeclaration(root_ast);
        break;
    case SYM_K_FUNC:
        parse_FuncDeclaration(root_ast);
        break;
    default:
        reportError(ERR_PARSER_DONOT_HANDLE_SYMBOL);
    }
}

/**
 *  ValDeclaration =
 *      ValKeyWord Identifier ":" TypeSpecifier "=" Expression
 *  ;
 */
void Parser::parse_ValDeclaration(AST* root_ast)
{
    if (accept(SYM_K_VAL, ERR_KW_VAL_EXPECTED))
    {
        if (accept(SYM_IDENTIFIER, ERR_IDENTIFIER_EXPECTED, !SKIP_EOL, !CONSUME))
        {
            AST* val_node = new AST(AST::Token::TOKEN_VAL_DECL, "?");
            root_ast->addChild(val_node);
            AstNodeId* id_node = new AstNodeId(sym.name);
            val_node->addChild(id_node);
            getSym();

            if (accept(SYM_COLON, ERR_COLON_EXPECTED))
            {
                if (accept(SYM_IDENTIFIER, ERR_TYPE_SPECIFIER_EXPECTED, !CONSUME))
                {
                    val_node->token.str = sym.name;
                    getSym();

                    if (accept(SYM_ASSIGN, ERR_ASSIGN_EXPECTED))
                    {
                        parse_Expression(val_node);
                    }
                }
            }
        }
    }
}

bool Parser::parse_Literal(AST* root_ast, bool report_error)
{
    bool parsed(true);

    ScanSymType types[] = {
        SYM_LIT_NUMBER,
        SYM_LIT_STRING,
        SYM_K_TRUE,
        SYM_K_FALSE,
    };

    ScanSymType foundType = SYM__ILLEGAL;
    bool found = lookFor(types, sizeof_array(types), foundType);

    if (!found && !isDone()) {
        if (report_error) {
            reportUnexpectedSymError(foundType, types, sizeof_array(types));
        }
        return false;
    }

    switch (foundType) {
    case SYM_K_TRUE:
        root_ast->addChild( new AST(AST::Token::TOKEN_LIT_BOOL, sym.name) );
        accept(SYM_K_TRUE);
        break;
    case SYM_K_FALSE:
        root_ast->addChild( new AST(AST::Token::TOKEN_LIT_BOOL, sym.name) );
        accept(SYM_K_FALSE);
        break;
    case SYM_LIT_NUMBER:
        root_ast->addChild( new AST(AST::Token::TOKEN_LIT_NUMBER, sym.name) );
        accept(SYM_LIT_NUMBER);
        break;
    case SYM_LIT_STRING:
        root_ast->addChild( new AST(AST::Token::TOKEN_LIT_STRING, sym.name) );
        accept(SYM_LIT_STRING);
        break;

    default:
        parsed = false;
        if (report_error) {
            reportError(ERR_PARSER_DONOT_HANDLE_SYMBOL);
        }
    }

    return parsed;
}

/** Expression.
 *
 *  Expression =
 *      MultExpr (("+"|"-") MultExpr)* ";"
 *  ;
 */
void Parser::parse_Expression(AST* root_ast)
{
parse_MultExpr(root_ast);

}

/** Multiply Expression.
 *
 *  MultExpr =
 *      Primary (("*"|"/") Primary)*
 *  ;
 */
void Parser::parse_MultExpr(AST* root)
{
    if (parse_Primary(root)) {

        ScanSymType mult_op[] = {
            SYM_STAR,
            SYM_SLASH,
        };
    
        ScanSymType foundType = SYM__ILLEGAL;
        bool found = lookFor(mult_op, sizeof_array(mult_op), foundType);
    
        if (found) {
            assert(!root->children.empty());

            AST** left_node = root->children.back();

            AST* op_node = new AST(AST::Token::TOKEN_OP, sym.name);
            op_node->addChild(*left_node);
            *left_node = op_node;

            getSym();
 
            parse_Primary(op_node);
        }

    }
}

/** Primary.
 *
 *  Primary =
 *      Literal | ID
 *  ;
 */
bool Parser::parse_Primary(AST* root)
{
    bool parsed(true);

    bool is_literal = try_parse_Literal(root);

    if (!is_literal) {
        if (accept(SYM_IDENTIFIER, ERR_IDENTIFIER_EXPECTED, !CONSUME))
        {
            AstNodeId* id_node = new AstNodeId(sym.name);
            root->addChild(id_node);
            getSym();
        }
        else {
            parsed = false;
        }
    }

    return parsed;
}

/**
 *  FuncDeclaration =
 *      FuncKeyWord Identifier "(" ")" ":" "(" ")" "{" FuncBody "}"
 *  ;
 */
void Parser::parse_FuncDeclaration(AST* root_ast)
{PRINT("+++++++++++\n");
    if (accept(SYM_K_FUNC, ERR_KW_FUNC_EXPECTED))
    {PRINT("--------------------\n");
        if (accept(SYM_IDENTIFIER, ERR_IDENTIFIER_EXPECTED, !CONSUME))
        {
#if 0
            AST* val_node = new AST(AST::Token::TOKEN_VAL_DECL, "?");
            root_ast->addChild(val_node);
            AstNodeId* id_node = new AstNodeId(sym.name);
            val_node->addChild(id_node);
            getSym();

            if (accept(SYM_COLON, ERR_COLON_EXPECTED))
            {
                if (accept(SYM_IDENTIFIER, ERR_TYPE_SPECIFIER_EXPECTED, !CONSUME))
                {
                    val_node->token.str = sym.name;
                    getSym();

                    if (accept(SYM_ASSIGN, ERR_ASSIGN_EXPECTED))
                    {
                        parse_Expression(val_node);
                    }
                }
            }
#endif
        }
    }
}


/**@file
 * @brief     LL(1) Parser for syntax analysis.
 * @author    Igor Lesik.
 * @copyright Igor Lesik 2011-2012.
 *
 * The "syntax analyzer" or "parser" groups the tokens produced by the scanner
 * into syntactic structures.
 */
#include "Parser.h"

//#include "defines.h"
#include "SrcRead.h"
#include "ast.h"
#include "ErrReport.h"
#include "debug.h"

static const bool CONSUME = true;
static const bool SKIP_EOL = true;

#ifdef NDEBUG
    static inline void debug(uint64_t flags, const char* frmt, ...) {}
#else
    #define debug(flags, frmt, ...)\
        debugModule(DBG_PARSE | flags, "parse", frmt, ##__VA_ARGS__)
#endif

void Parser_create(Parser* self, SrcReader* srcReader, ErrReport* err, Scanner* scanner)
{
    self->srcReader = srcReader;
    self->errReport = err;
    self->scanner   = scanner;
}

void Parser_destroy(Parser* self)
{
}

static inline
bool Parser_isDone(Parser* self)
{
    return (self->errReport->isError || self->sym.type == SYM_EOF);
}

static inline
bool isSkippableType(ScanSymType type)
{
    return
        type == SYM_EOL_COMMENT
     || type == SYM_MULTI_COMMENT
     || type == SYM_EOL
   ;
}

static inline
void getSym(Parser* self)
{
    Scanner_getSym(self->scanner, &self->sym);
}

static inline
void reportError(Parser* self, int errCode, const char* location, int line)
{
    ErrReport_report(self->errReport, errCode);
    debug(DBG_L_ERR, "error location:%s line %d\n", location, line);
}

bool Parser_accept(Parser* self, ScanSymType type, int errCode, bool skip_eol, bool consume)
{
    Symbol* sym = &self->sym;

    //if (isDone())
    //    return false;

    // Skip comments.
    while (sym->type != type && isSkippableType(sym->type)) {
        if (!skip_eol && (sym->type == SYM_EOL || sym->type == SYM_EOL_COMMENT))
            break;
        debug(DBG_L_DBG, "symbol(%-8s):%s\n", symName(sym->type), sym->name);
        getSym(self);
    }

    if (sym->type == type) {
        debug(DBG_L_DBG, "symbol(%-8s):%s\n", symName(sym->type), sym->name);
        if (consume) getSym(self);
        return true;
    }
    else {
        reportError(self, errCode, __FUNCTION__, __LINE__);
        return false;
    }
}


bool Parser_lookFor(Parser* self, ScanSymType types[], size_t size, ScanSymType* foundType)
{
    size_t i;

    *foundType = SYM__ILLEGAL;

    // Skip comments.
    while (isSkippableType(self->sym.type)) {
        debug(DBG_L_DBG, "symbol(%-8s):%s\n", symName(self->sym.type), self->sym.name);
        getSym(self);
    }

    *foundType = self->sym.type;

    for (i = 0; i < size; ++i) {
        if (self->sym.type == types[i]) {
            debug(DBG_L_DBG, "found expected symbol %s:%s\n",
                symName(self->sym.type), self->sym.name);
            return true;
        }
    }

    return false;
}

void Parser_reportUnexpectedSymError(
    Parser* self,
    ScanSymType type,
    ScanSymType expectedTypes[],
    size_t size)
{
    size_t i;

    reportError(self, ERR_UNEXPECTED_SYMBOL, __FUNCTION__, __LINE__);

    PRINT("Error: unexpected symbol %s, expected:", symName(type));

    for (i = 0; i < size; ++i) {
        assert(i < SYM__END);
        PRINT(" %s,", symName(expectedTypes[i]));
    }

    PRINT("\n");
}

/**
 *  ClassBody =
 *      ImportStatement
 *    | NestedPackage
 *    | FuncDeclaration
 *    | ValDeclaration
 *  ;
 */
void Parser_parse_ClassBody(Parser* self, AST* root_ast)
{
    ScanSymType types[] = {
        SYM_K_VAR,
        SYM_K_VAL,
        SYM_END
    };

    ScanSymType foundType = SYM__ILLEGAL;
    bool found = Parser_lookFor(self, types, sizeof_array(types), &foundType);

    if (!found && !Parser_isDone(self)) {
        Parser_reportUnexpectedSymError(self, foundType, types, sizeof_array(types));
        return;
    }

    debug(DBG_L_DBG, "found type %s\n", symName(foundType));

    switch (foundType) {
    case SYM_K_VAL:
        //parse_ClassValDeclaration(root_ast);
        break;
    case SYM_K_VAR:
        //parse_ClassVarDeclaration(root_ast);
        break;
    case SYM_END:
        getSym(self); return; //FIXME
    default:
        reportError(self, ERR_PARSER_CANT_HANDLE_SYMBOL, __FUNCTION__, __LINE__);
    }
}
/**
 *  ClassDefinition =
 *      ClassKeyWord Identifier "{" ClassBody
 *  ;
 */
void Parser_parse_ClassDefinition(Parser* self, AST* root_ast)
{
    if (Parser_accept(self, SYM_K_CLASS, ERR_KW_CLASS_EXPECTED, !SKIP_EOL, CONSUME))
    {
        if (Parser_accept(self, SYM_IDENTIFIER, ERR_IDENTIFIER_EXPECTED, !SKIP_EOL, !CONSUME))
        {
            AST* class_ast = AST_new(TOKEN_CLASS, self->sym.name);
            AST_addChild(root_ast, class_ast);
            getSym(self);

            if (Parser_accept(self, SYM_BEGIN, ERR_BEGIN_EXPECTED, SKIP_EOL, CONSUME) )
            {
                Parser_parse_ClassBody(self, class_ast);
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
void Parser_parse_PackageBody(Parser* self, AST* root_ast)
{
    ScanSymType types[] = {
        //SYM_K_IMPORT,
        //SYM_K_PACKAGE,
        //SYM_K_FUNC,
        //SYM_K_VAL,
        SYM_K_CLASS
    };

    ScanSymType foundType = SYM__ILLEGAL;
    bool found = Parser_lookFor(self, types, sizeof_array(types), &foundType);

    if (!found && !Parser_isDone(self)) {
        Parser_reportUnexpectedSymError(self, foundType, types, sizeof_array(types));
        return;
    }

    debug(DBG_L_DBG, "found type %s\n", symName(foundType));

    switch (foundType) {
    /*case SYM_K_VAL:
        parse_ValDeclaration(root_ast);
        break;
    case SYM_K_FUNC:
        parse_FuncDeclaration(root_ast);
        break;*/
    case SYM_K_CLASS:
        Parser_parse_ClassDefinition(self, root_ast);
        break;
    case SYM_EOF:
        break;
    default:
        reportError(self, ERR_PARSER_CANT_HANDLE_SYMBOL, __FUNCTION__, __LINE__);
    }
}

/**
 *  TopPackage =
 *      "package" PackageId EOL PackageBody
 *  ;
 *
 */
void Parser_parse_TopPackage(Parser* self, AST* root_ast)
{
    if (Parser_accept(self, SYM_K_PACKAGE, ERR_KW_PACKAGE_EXPECTED, SKIP_EOL, CONSUME) )
    {
        if (Parser_accept(self, SYM_IDENTIFIER, ERR_IDENTIFIER_EXPECTED, !SKIP_EOL, !CONSUME) )
        {
            AST* ast = AST_new(TOKEN_PKG, self->sym.name);
            AST_addChild(root_ast, ast);
            getSym(self);

            if (Parser_accept(self, SYM_EOL, ERR_EOL_EXPECTED, SKIP_EOL, CONSUME) )
            {
                while (!Parser_isDone(self)) {
                    Parser_parse_PackageBody(self, ast);
                }
            }
        }
    }
}
#if 0


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
#endif

void Parser_parse(Parser* self, AST* ast)
{
    self->sym.type = SYM_EOF;

    // kick off Reader, read 1st character
    SrcReader_nextChar(self->srcReader);

    // kick off Scanner, get 1st symbol
    getSym(self);

    Parser_parse_TopPackage(self, ast);
}


#include "cell.h"

using namespace ulisp;

const Cell Cell::false_sym(T_SYMBOL, "#f");
const Cell Cell::true_sym(T_SYMBOL, "#t"); 
const Cell Cell::nil(T_SYMBOL, "nil");

#define SYM__TYPE(name) #name
static const char* symtype2str[] = {
#include "symtype.h"
,NULL
};
#undef SYM__TYPE

const char* Cell::type2str(CellType type){ return symtype2str[type]; }

// convert given cell to a Lisp-readable string
std::string
Cell::
to_string() const
{
    const Cell& exp = *this;

    if (exp.type == Cell::T_LIST)
    {
        std::string s("(");
        for (Cell::Iter e = exp.list.begin(); e != exp.list.end(); ++e) {
            s += (*e)->to_string() + ' ';
        }
        if (s[s.size() - 1] == ' ')
            s.erase(s.size() - 1);
        return s + ')';
    }
    else if (exp.type == Cell::T_LAMBDA)
        return "<Lambda>";
    else if (exp.type == Cell::T_PROC)
        return "<Proc>";
    return exp.val;
}

// convert given string to list of tokens
//
static
void tokenize(const char* str, std::list<std::string>& tokens)
{
    const char* s = str;

    while (*s)
    {
        while (*s == ' ')
            ++s;
        if (*s == '(' || *s == ')')
            tokens.push_back(*s++ == '(' ? "(" : ")");
        else {
            const char* t = s;
            while (*t && *t != ' ' && *t != '(' && *t != ')')
                ++t;
            tokens.push_back(std::string(s, t));
            s = t;
        }
    }

}

// return the Lisp expression represented by the given string
void
Cell::
parse(CellFactory& factory, const char* input)
{
    std::list<std::string> tokens;
    tokenize(input, tokens);

    return read(factory, tokens);
}

// construct the Lisp expression in the given tokens
void
Cell::
read(CellFactory& factory, std::list<std::string>& tokens)
{
    const std::string token(tokens.front());

    tokens.pop_front();

    if (token == "(")
    {
        this->type = Cell::T_LIST;
        while (tokens.front() != ")") {
            Cell& cell = factory.make();
            cell.read(factory, tokens);
            this->list.push_back(&cell);
        }
        tokens.pop_front();
    }
    else
    {
        construct_atom(token);
    }
}

// return true iff given character is '0'..'9'
static inline
bool isdig(char c) { return isdigit(static_cast<unsigned char>(c)) != 0; }

// numbers become Numbers; every other token is a Symbol
void Cell::construct_atom(const std::string& token)
{
    if (isdig(token[0]) || (token[0] == '-' && isdig(token[1])))
    {
        this->type = Cell::T_NUMBER;
        this->val = token;
    }
    else
    {
        this->type = Cell::T_SYMBOL;
        this->val = token;
    }
}

/**@file
 * @brief     Symbol management
 * @author    Igor Lesik 2017
 * @copyright Igor Lesik 2017
 *
 *
 *
 */
#include "igr.h"

/** Location inside a source code file.
 *
 */
typedef struct Coordinate
{
    char* file; ///< source code file
    uint x;     ///< row
    uint y;     ///< line # in the file
}
Coordinate;

typedef struct Symbol* Symbol;

/** Source code symbol.
 *
 */
struct Symbol
{
    char* name;     ///< name as in input source code
    Coordinate src; ///< location inside source code
};

typedef struct SymTable SymTable;

struct SymTable
{
    int level;
    SymTable* previous;

    struct Entry {
        Symbol sym;
        struct Entry* link;
    } *buckets[256];
};

#define SYMTABLE_HASHSIZE sizeof_array(((SymTable*)0)->buckets)

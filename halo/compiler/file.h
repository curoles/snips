/**@file
 * File operations.
 * Copyright (C) 2010 Soft Machines Inc.
 *
 */
#ifndef FILE_H_INCLUDED
#define FILE_H_INCLUDED

#include <string.h>
#include <stdlib.h>
#include <stdio.h>

class File
{
public:
    typedef long int pos_t;

    static const pos_t NPOS = -1; 

public:
    bool open(const char* filename, const char* mode) {
        file = fopen(filename, mode);
        return (file != NULL);
    }

    void close() {
        if (file != NULL) {
            fclose(file);
            file = NULL;
        }
    }

    bool isOpen() { return file != NULL; }

    bool eof() { return feof(file); }

    operator FILE* () { return file; }

    void assign(FILE* fd) { file = fd; }
    void release() { file = NULL; }

    File():file(NULL){}
    File(const File& that):file(that.file){}
   ~File() { File::close(); }

private:
    FILE* file;
};

template<class T> bool fread_val(File& file, T& val)
{
    return fread( (void*)&val, sizeof(val), 1, file);
}
 
template<class T> bool fread_val(File& file, File::pos_t pos, T& val)
{
    if (0 != fseek(file, pos, SEEK_SET))
        return false;

    return fread((void*)&val, sizeof(val), 1, file);
}

template<class T> bool fwrite_val(File& file, T& val)
{
    return fwrite((void*)&val, sizeof(val), 1, file);
}

#endif // FILE_H_INCLUDED


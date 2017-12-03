/**@file
 *
 */
#pragma once
#ifndef HALO_ZTRING_H
#define HALO_ZTRING_H

#include <string.h>
#include <stdlib.h>
#include <assert.h>

class string
{
public:
    string(const char* s = "") { mem = strdup(s? s:""); assert(mem); }
   ~string() { free(mem); }

    void operator=(const char* s) {
        free(mem);
        mem = strdup(s? s:"");
        assert(mem); 
    }

    void operator=(const string& s) {
        operator=(s.c_str());
    }

    bool operator==(const char* s) {
        return 0 == strcmp(mem, s);
    }

    size_t length() const {
        return strlen(mem);
    }

    bool empty() const { return length() == 0; }

    void append(const char* s) {
        size_t old_len = length(), sufx_len = strlen(s);
        size_t new_len = old_len + sufx_len + 1;
        mem = (char*)realloc(mem, new_len);
        assert(mem);
        strncpy(mem + old_len, s, sufx_len + 1);
    }

    operator const char* () {
        return mem;
    }

    const char* c_str() const {
        return mem;
    }

    void stripSuffix(char delim = '.') {
        size_t len = length();
        while (len > 0) {
            --len;
            if (mem[len] == delim) { mem[len]='\0'; break; }
        }
    }

private:
    char* mem;

    string(const string&);
};

#endif

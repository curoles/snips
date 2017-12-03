/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012
 *
 */
#pragma once
#ifndef COH_FILE_H_INCLUDED
#define COH_FILE_H_INCLUDED

#include "COH.h"

#include <errno.h>
#include <string.h>
#include <stdbool.h>
#include <assert.h>

typedef error_t (*file_action_t)(FILE*);

static inline
error_t
withFile(FILE* log, const char* file_path, const char* mode, file_action_t file_action)
{
    FILE* f = fopen(file_path, mode? mode:"w");

    if (!f)
    {
        if (log)
        {
            fprintf(log, "Error: %s\n", strerror(errno));
        }

        return ERR_NO_FILE;
    }

    error_t ret = (*file_action)(f);

    fclose(f);

    return ret;
}

struct File
{
    FILE* fd;
};
typedef struct File File;

static inline
void File_create(File* self)
{
    self->fd = NULL;
}

static inline
bool File_open(File* self, const char* file_path, const char* mode)
{
    assert(self);
    assert(!self->fd);
    self->fd = fopen(file_path, mode);
    return self->fd;
}

static inline
void File_close(File* self)
{
    if (self->fd)
    {
        fclose(self->fd);
        self->fd = NULL;
    }
}

static inline
void File_destroy(File* self)
{
    if (self->fd)
    {
        File_close(self);
    }
}
#endif //  COH_FILE_H_INCLUDED

/**@file
 * @brief     Report error.
 * @author    Igor Lesik.
 * @copyright Igor Lesik 2011-2012.
 *
 */
#pragma once
#ifndef COH_ERREPORT_H_INCLUDED
#define COH_ERREPORT_H_INCLUDED

#include "SrcRead.h"

/** Print out error message and set sticky error flag.
 *
 * Has a reference to SrcReader and calls SrcReader's printer just
 * because it knows better what place error happened.
 */
struct ErrReport
{
    /// Sticky flag that says that error occurred.
    bool isError;

    /// Source readers knows where in the source text the error is.
    SrcReader* srcReader;
};
typedef struct ErrReport ErrReport;

static inline
void ErrReport_create(ErrReport* self, SrcReader* srcReader)
{
    self->isError = false;
    self->srcReader = srcReader;
}

static inline
void ErrReport_destroy(ErrReport* self){}

/// Print out error message and set sticky error flag.
static inline
void ErrReport_report(ErrReport* self, int errorCode)
{
    SrcReader_reportError(self->srcReader, errorCode);
    self->isError = true;
}



#endif

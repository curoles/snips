/**@file
 * Report error.
 * Copyright (C) 2011 Igor Lesik.
 *
 */
#pragma once
#ifndef HALO_ERREPORT_H_INCLUDED
#define HALO_ERREPORT_H_INCLUDED

#include "srcread.h"

/** Print out error message and set sticky error flag.
 *
 */
class ErrReport
{
public:
    bool isError() const { return m_isError; }

    /// Print out error message and set sticky error flag.
    void report(int errorCode) {
        m_srcReader.reportError(errorCode);
        m_isError = true;
    }

    ErrReport(SrcReader& sr):m_isError(false), m_srcReader(sr) {}

private:
    /// Sticky flag that says that error occured.
    bool m_isError;

    /// Source readers knows where in the source text the error is.
    SrcReader& m_srcReader;
};


#endif

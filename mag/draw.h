#pragma once

#include <stdint.h>
#include <stddef.h>

#include "image.h"

typedef struct GPoint
{
    int x, y;
}
GPoint;

typedef struct GLine
{
    GPoint currentPoint;
    size_t width;
    Pixel clr;
}
GLine;

void GLine_drawTo(
    Image* image,
    GLine* line,
    int x_to, int y_to
);

static inline
void GLine_drawFromTo(
    Image* image,
    GLine* line,
    int x_from, int y_from, int x_to, int y_to
)
{
    line->currentPoint.x = x_from;
    line->currentPoint.y = y_from;
    GLine_drawTo(image, line, x_to, y_to);
}

static inline
void GLine_drawFromTo2(Image* image, GLine* line, GPoint begin, GPoint end) {
    GLine_drawFromTo(image, line, begin.x, begin.y, end.x, end.y);
}

static inline
void GLine_drawTo2(Image* image, GLine* line, GPoint end) {
    GLine_drawTo(image, line, end.x, end.y);
}



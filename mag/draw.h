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
    Pixel pxl;
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
    Pixel* pixel,
    int x_from, int y_from, int x_to, int y_to
)
{
    GLine line;
    line.currentPoint.x = x_from;
    line.currentPoint.y = y_from;
    line.pxl = *pixel;
    GLine_drawTo(image, &line, x_to, y_to);
}

static inline
void GLine_drawFromTo2(Image* image, Pixel* pixel, GPoint begin, GPoint end) {
    GLine_drawFromTo(image, pixel, begin.x, begin.y, end.x, end.y);
}

static inline
void GLine_drawTo2(Image* image, GLine* line, GPoint end) {
    GLine_drawTo(image, line, end.x, end.y);
}


void
GCircle_draw(
    Image* image,
    Pixel* pixel,
    int xm, int ym,
    int r
);

void
GRing_draw(
    Image* image,
    Pixel* pixel,
    int xm, int ym,
    unsigned int intR,
    unsigned int extR
);

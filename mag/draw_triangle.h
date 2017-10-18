#pragma once

#include "image.h"
#include "draw.h"

/*typedef struct Vertice
{
    int x, y;
}
Vertice;*/
typedef struct GPoint Vertice;

void
GTriangle_drawFilled(
    Image* image,
    Pixel* pixel,
    Vertice v1,
    Vertice v2,
    Vertice v3
);

static inline
void
GTriangle_drawFilled2(
    Image* image,
    Pixel* pixel,
    int v1x, int v1y,
    int v2x, int v2y,
    int v3x, int v3y
)
{
    Vertice v1 = {v1x, v1y}; Vertice v2 = {v2x, v2y}; Vertice v3 = {v3x, v3y};
    GTriangle_drawFilled(image, pixel, v1, v2, v3);
}


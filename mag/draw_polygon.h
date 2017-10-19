/**@file
 * @brief     Draw polygons.
 * @author    Igor Lesik 2017.
 * @copyright TODO
 *
 */
#pragma once

#include "draw_triangle.h"

void
G4gon_drawFilled(
    Image* image,
    Pixel* pixel,
    Vertice v1,
    Vertice v2,
    Vertice v3,
    Vertice v4
);

// Sides aligned with X-Y axis.
void
GRect_drawFilled(
    Image* image,
    Pixel* pixel,
    Vertice botLeft,
    Vertice topRight
);

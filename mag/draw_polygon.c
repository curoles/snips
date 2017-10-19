/**@file
 * @brief     Draw polygons.
 * @author    Igor Lesik 2017.
 * @copyright TODO
 *
 */
#include "draw_polygon.h"

void
G4gon_drawFilled(
    Image* image,
    Pixel* pixel,
    Vertice v1,
    Vertice v2,
    Vertice v3,
    Vertice v4
)
{
    GTriangle_drawFilled(image, pixel, v1, v2, v3);
    GTriangle_drawFilled(image, pixel, v3, v4, v1);
}

void
GRect_drawFilled(
    Image* image,
    Pixel* pixel,
    Vertice botLeft,
    Vertice topRight
)
{
    Vertice v1 = {botLeft.x, botLeft.y};
    Vertice v2 = {botLeft.x, topRight.y};
    Vertice v3 = {topRight.x, topRight.y};
    Vertice v4 = {topRight.x, botLeft.y};

    G4gon_drawFilled(image, pixel, v1, v2, v3, v4);
}

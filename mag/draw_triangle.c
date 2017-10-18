//http://www.sunshine2k.de/coding/java/TriangleRasterization/TriangleRasterization.html
#include "draw_triangle.h"

#include <stdbool.h>
#include <stdlib.h>

#include "image.h"

#define assert(x)

#define SIGNUM(x) (((x) > 0) - ((x) < 0))

#define max(a,b) \
   ({ __typeof__ (a) _a = (a); \
       __typeof__ (b) _b = (b); \
     _a > _b ? _a : _b; })

#define min(a,b) \
   ({ __typeof__ (a) _a = (a); \
       __typeof__ (b) _b = (b); \
     _a < _b ? _a : _b; })

static
void sortVerticesAscendingByY(
    Vertice* v1,
    Vertice* v2,
    Vertice* v3
)
{
    Vertice vTmp;
    
    if (v1->y > v2->y)
    {
        vTmp = *v1;
        *v1 = *v2;
        *v2 = vTmp;
    }
    assert(v1.y <= v2.y);

    if (v1->y > v3->y)
    {
        vTmp = *v1;
        *v1 = *v3;
        *v3 = vTmp;
    }
    assert(v1.y <= v2.y && v1.y <= v3.y);

    // test v2 vs. v3
    if (v2->y > v3->y)
    {
        vTmp = *v2;
        *v2 = *v3;
        *v3 = vTmp;
    }
}


/**
 * This method rasterizes a triangle using only integer variables by using a
 * modified Bresenham algorithm.
 * It's important that v2 and v3 lie on the same horizontal line, that is
 * v2.y must be equal to v3.y.
 * @param g Graphics object
 * @param v1 vertice of triangle
 * @param v2 vertice of triangle, must have same y-coordinate as v3.
 * @param v3 vertice of triangle, must have same y-coordinate as v2.
 */
static
void
fillFlatSideTriangle(
    Image* image,
    Pixel* pixel,
    Vertice v1,
    Vertice v2,
    Vertice v3
)
{
    Vertice vTmp1 = {v1.x, v1.y};
    Vertice vTmp2 = {v1.x, v1.y};
    
    bool changed1 = false;
    bool changed2 = false;
    
    int dx1 = abs(v2.x - v1.x);
    int dy1 = abs(v2.y - v1.y);
    
    int dx2 = abs(v3.x - v1.x);
    int dy2 = abs(v3.y - v1.y);
    
    int signx1 = SIGNUM(v2.x - v1.x);
    int signx2 = SIGNUM(v3.x - v1.x);
    
    int signy1 = SIGNUM(v2.y - v1.y);
    int signy2 = SIGNUM(v3.y - v1.y);
    
    if (dy1 > dx1)
    {   // swap values
        int tmp = dx1;
        dx1 = dy1;
        dy1 = tmp;
        changed1 = true;
    }
    
    if (dy2 > dx2)
    {   // swap values
        int tmp = dx2;
        dx2 = dy2;
        dy2 = tmp;
        changed2 = true;
    }
    
    int e1 = 2 * dy1 - dx1;
    int e2 = 2 * dy2 - dx2;
    
    for (int i = 0; i <= dx1; i++)
    {
        //drawLine(vTmp1.x, vTmp1.y, vTmp2.x, vTmp2.y);
        int x_right = max(vTmp1.x, vTmp2.x);
        for (int x = min(vTmp1.x,vTmp2.x); x <= x_right; x++) {
            Image_setSafe(image, x, vTmp1.y, pixel);
        }
        
        while (e1 >= 0)
        {
            if (changed1)
                vTmp1.x += signx1;
            else
                vTmp1.y += signy1;
            e1 = e1 - 2 * dx1;
        }
        
        if (changed1)
            vTmp1.y += signy1;
        else
            vTmp1.x += signx1;  
      
        e1 = e1 + 2 * dy1;
        
        /* here we rendered the next point on line 1 so follow now line 2
         * until we are on the same y-value as line 1.
         */
        while (vTmp2.y != vTmp1.y)
        {
            while (e2 >= 0)
            {
                if (changed2)
                    vTmp2.x += signx2;
                else
                    vTmp2.y += signy2;
                e2 = e2 - 2 * dx2;
            }

            if (changed2)
                vTmp2.y += signy2;
            else
                vTmp2.x += signx2;

            e2 = e2 + 2 * dy2;
        }
    }
    
}

void
GTriangle_drawFilled(
    Image* image,
    Pixel* pixel,
    Vertice v1,
    Vertice v2,
    Vertice v3
)
{
    
    /* at first sort the three vertices by y-coordinate ascending, 
     * so p1 is the topmost vertice */
    sortVerticesAscendingByY(&v1, &v2, &v3);
    
    /* here we know that v1.y <= v2.y <= v3.y */
    /* check for trivial case of bottom-flat triangle */
    if (v2.y == v3.y)
    {
        fillFlatSideTriangle(image, pixel, v1, v2, v3);
    }
    /* check for trivial case of top-flat triangle */
    else if (v1.y == v2.y)
    {
        fillFlatSideTriangle(image, pixel, v3, v1, v2);
    } 
    else
    {
        /* general case - split the triangle in a topflat and bottom-flat one */
        Vertice vTmp = { 
            (int)(v1.x + ((float)(v2.y - v1.y) / (float)(v3.y - v1.y)) * (v3.x - v1.x)),
            v2.y
        };
        fillFlatSideTriangle(image, pixel, v1, v2, vTmp);
        fillFlatSideTriangle(image, pixel, v3, v2, vTmp);
    }
}

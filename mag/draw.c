//https://www.cs.helsinki.fi/group/goa/mallinnus/lines/gsoft2.html
//https://www.cs.helsinki.fi/group/goa/mallinnus/lines/bresenh.html
//
#include "draw.h"

#include <stdlib.h>
//#include <stdio.h>

#if 0
void GLine_drawTo(
    Image* image,
    GLine* line,
    int x2, int y2
)
{
    size_t w = (image->xres > image->yres)? image->xres : image->yres;
    int x1 = line->currentPoint.x;
    int y1 = line->currentPoint.y;

    long x = x1*w + w/2;
    long y = y1*w + w/2;

    long dx = x2 - x1,
         dy = y2 - y1;
  
    for (size_t i = 0; i < w; i++)  {
        Image_set(image, x/w, y/w, &line->clr);
        x += dx;  y += dy;
    }

    line->currentPoint.x = x2;
    line->currentPoint.y = y2;
}
#endif

//https://en.wikipedia.org/wiki/Bresenham%27s_line_algorithm
//https://gist.github.com/bert/1085538
//
//
void GLine_drawTo(
    Image* image,
    GLine* line,
    int x1, int y1
)
{
    int x0 = line->currentPoint.x;
    int y0 = line->currentPoint.y;

    int dx =  abs (x1 - x0), sx = x0 < x1 ? 1 : -1;
    int dy = -abs (y1 - y0), sy = y0 < y1 ? 1 : -1; 
    int err = dx + dy, e2; /* error value e_xy */
 
    for (;;) {  /* loop */
        Image_set(image, x0, y0, &line->pxl);
        if (x0 == x1 && y0 == y1) break;
        e2 = 2 * err;
        if (e2 >= dy) { err += dy; x0 += sx; } /* e_xy+e_x > 0 */
        if (e2 <= dx) { err += dx; y0 += sy; } /* e_xy+e_y < 0 */
    }

    line->currentPoint.x = x1;
    line->currentPoint.y = y1;
}

#define setPixel(x, y) Image_setSafe(image, x, y, pixel)

void
GCircle_draw(
    Image* image,
    Pixel* pixel,
    int xm, int ym,
    int r
)
{
    //printf("Draw circle x=%d y=%d R=%d\n", xm, ym, r); fflush(stdout);

    int x = -r, y = 0, err = 2-2*r; /* II. Quadrant */ 
    do {
        setPixel (xm-x, ym+y); /*   I. Quadrant */
        setPixel (xm-y, ym-x); /*  II. Quadrant */
        setPixel (xm+x, ym-y); /* III. Quadrant */
        setPixel (xm+y, ym+x); /*  IV. Quadrant */
        r = err;
        if (r >  x) err += ++x*2+1; /* e_xy+e_x > 0 */
        if (r <= y) err += ++y*2+1; /* e_xy+e_y < 0 */
    } while (x < 0);
}

void
GRing_draw(
    Image* image,
    Pixel* pixel,
    int xm, int ym,
    unsigned int intR,
    unsigned int extR
)
{
    for (unsigned int r = intR; r <= extR; r++) {
        GCircle_draw(image, pixel, xm, ym, r);
    }
}

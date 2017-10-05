//http://www.donrelyea.com/hilbert_algorithmic_art_menu.htm
//http://mathworld.wolfram.com/HilbertCurve.html
//http://www.fundza.com/algorithmic/space_filling/hilbert/basics/index.html
//
//
//

#include "hilbert.h"

/* x and y are the coordinates of the bottom left corner */
/* xi & xj are the i & j components of the unit x vector of this frame */
/* similarly yis and yjs */
void hilbert(
    Image* image,
    GLine* line,
    double x,  double y,
    double xi, double xj,
    double yi, double yj,
    size_t n
)
{
    if (n <= 0) {
        GLine_drawTo(image, line, x + (xi + yi)/2, y + (xj + yj)/2);
    }
    else {
        hilbert(image, line, x,           y,           yi/2, yj/2,  xi/2,  xj/2, n-1);
        hilbert(image, line, x+xi/2,      y+xj/2 ,     xi/2, xj/2,  yi/2,  yj/2, n-1);
        hilbert(image, line, x+(xi+yi)/2, y+(xj+yj)/2, xi/2, xj/2,  yi/2,  yj/2, n-1);
        hilbert(image, line, x+xi/2+yi,   y+xj/2+yj,  -yi/2,-yj/2, -xi/2, -xj/2, n-1);
    }
}

/* Sample call */
//hilbert(0, 0, 300, 0, 0, 300, 4);

#if 0
void hilbert(
    Image* image,
    GLine* line,
    double x,  double y,
    double xi, double xj,
    double yi, double yj,
    size_t n
)
{
    while (n >= 0) {
        hilbert(x0, y0, yis/2, yjs/2, xis/2, xjs/2, n);
        lineFromTo( point(x0+xis/2, y0+xjs/2), point(x0+(xis+yis)/2, y0+(xjs+yjs)/2));
hilbert_draw(x0+xis/2, y0+xjs/2 ,xis/2, xjs/2, yis/2, yjs/2, n-1)
draw_from_to_numsteps( point(x0+xis/2, y0+xjs/2), point(x0+(xis+yis)/2, y0+(xjs+yjs)/2), numsteps)
hilbert_draw(x0+xis/2+yis/2, y0+(xjs/2)+(yjs/2), xis/2, xjs/2, yis/2, yjs/2,n-1)
draw_from_to_numsteps( point(x0+(xis/2)+(yis/2), y0+(xjs/2)+(yjs/2)), point(x0+(xis+yis)/2, y0+(xjs+yjs)/2), numsteps)
hilbert_draw(x0+(xis/2)+yis, y0+(xjs/2)+yjs, -yis/2,-yjs/2, -xis/2, -xjs/2,n-1)
draw_from_to_numsteps( point(x0+xis/2+yis, y0+xjs/2+yjs), point(x0+(xis+yis)/2, y0+(xjs+yjs)/2), numsteps)

        if (n == 0) break;
        n -= 1;
     }
}
#endif

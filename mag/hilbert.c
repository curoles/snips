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
static
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

void HilbertCurve_drawLine(
    Image* image,
    GLine* line,
    double x,  double y,
    double xi, double xj,
    double yi, double yj,
    size_t order
)
{
    hilbert(image, line, x, y, xi, xj, yi, yj, order);
}

/* Sample call */
//hilbert(0, 0, 300, 0, 0, 300, 4);

void HilbertCurve_visit(
    HilbertCurveVisitor visitor,
    void* context,
    double x,  double y,
    double xi, double xj,
    double yi, double yj,
    size_t n
)
{
    if (n <= 0) {
        visitor(context, x, y, x + (xi + yi)/2, y + (xj + yj)/2);
    }
    else {
        HilbertCurve_visit(visitor, context, x,           y,           yi/2, yj/2,  xi/2,  xj/2, n-1);
        HilbertCurve_visit(visitor, context, x+xi/2,      y+xj/2 ,     xi/2, xj/2,  yi/2,  yj/2, n-1);
        HilbertCurve_visit(visitor, context, x+(xi+yi)/2, y+(xj+yj)/2, xi/2, xj/2,  yi/2,  yj/2, n-1);
        HilbertCurve_visit(visitor, context, x+xi/2+yi,   y+xj/2+yj,  -yi/2,-yj/2, -xi/2, -xj/2, n-1);
    }
}

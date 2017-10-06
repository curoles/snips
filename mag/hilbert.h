#include <stddef.h>

#include "image.h"
#include "draw.h"

void HilbertCurve_drawLine(
    Image* image,
    GLine* line,
    double x,  double y,
    double xi, double xj,
    double yi, double yj,
    size_t order
);

typedef void (*HilbertCurveVisitor)(void* context, int x0, int y0, int x1, int y1);

void HilbertCurve_visit(
    HilbertCurveVisitor visitor,
    void* context,
    double x,  double y,
    double xi, double xj,
    double yi, double yj,
    size_t order
);


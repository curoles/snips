#include <stddef.h>

#include "image.h"
#include "draw.h"

void hilbert(
    Image* image,
    GLine* line,
    double x,  double y,
    double xi, double xj,
    double yi, double yj,
    size_t n
);

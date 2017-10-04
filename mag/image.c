#include "image.h"

#include <stdlib.h>

Image
Image_alloc(size_t x, size_t y)
{
    Image image;
    image.xres = x;
    image.yres = y;

    image.pixels = calloc(x*y, sizeof(Pixel));

    return image;
}

void
Image_free(Image* image)
{
    if (image != NULL && image->pixels != NULL) {
        free(image->pixels);
        image->pixels = NULL;
    }
}

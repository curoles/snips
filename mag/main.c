#include "image.h"
#include "write_to_tiff.h"

#include <stdlib.h>

void render(const Image* image)
{
    for (size_t row = 0; row < image->yres; row++)
    {
        for (size_t col = 0; col < image->xres; col++) {
            Image_row(image, row)[col].clr[0] = 255;
            Image_row(image, row)[col].clr[1] = 128;
            Image_row(image, row)[col].clr[2] = 50;
        }
    }
}

int main(int argc, char* argv[])
{
    Image image = Image_alloc(500, 500);

    render(&image);

    write_to_tiff("test1.tiff", &image);

    Image_free(&image);

    return EXIT_SUCCESS;
}

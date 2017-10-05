#include "image.h"
#include "draw.h"
#include "hilbert.h"
#include "write_to_tiff.h"

#include <stdlib.h>

void render(Image* image)
{
    for (size_t row = 0; row < image->yres; row++)
    {
        for (size_t col = 0; col < image->xres; col++) {
            Image_row(image, row)[col].clr[0] = 255;
            Image_row(image, row)[col].clr[1] = 128;
            Image_row(image, row)[col].clr[2] = 50;
        }
    }

    GLine line = {.clr.clr[RED]=0, .clr.clr[GREEN]=0, .clr.clr[BLUE]=0};
    //GLine_drawFromTo(image, &line, 0, 0, 250, 250);
    //GLine_drawFromTo(image, &line, 250, 250, 450, 250);
    //GLine_drawFromTo(image, &line, 450, 250, 450, 450);

    line.currentPoint.x = 0; line.currentPoint.y = 0;
    hilbert(image, &line, 0, 0, 500, 0, 0, 500, 6); 
}

int main(int argc, char* argv[])
{
    Image image = Image_alloc(500, 500);

    render(&image);

    write_to_tiff("test1.tiff", &image);

    Image_free(&image);

    return EXIT_SUCCESS;
}

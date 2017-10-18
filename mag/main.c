#include "image.h"
#include "draw.h"
#include "hilbert.h"
#include "draw_triangle.h"
#include "write_to_tiff.h"

#include <stdlib.h>

void drawSomething(void* context, int x0, int y0, int x1, int y1)
{
    Image* image = (Image*)context;

    Pixel pixel = {.clr[RED]=x1, .clr[GREEN]=y1, .clr[BLUE]=y1-x1};

    //GRing_draw(image, &pixel, x1, y1, 10, 20);
    GTriangle_drawFilled2(image, &pixel, x0, y0, x1, y1, y1, x0);
}

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

    Pixel blackPixel = {.clr[RED]=0, .clr[GREEN]=0, .clr[BLUE]=0};

    GLine line = {.pxl=blackPixel};
    //GLine_drawFromTo(image, &line, 0, 0, 250, 250);
    //GLine_drawFromTo(image, &line, 250, 250, 450, 250);
    //GLine_drawFromTo(image, &line, 450, 250, 450, 450);
    GCircle_draw(image, &blackPixel, 250, 250, 100);

    GTriangle_drawFilled2(image, &blackPixel, 0,0, 100,400, 300,300);

    line.currentPoint.x = 0; line.currentPoint.y = 0;
    HilbertCurve_drawLine(image, &line, 0, 0, 500, 0, 0, 500, 3);

    HilbertCurve_visit(drawSomething, image, 0, 0, 500, 0, 0, 500, 3);
}

int main(int argc, char* argv[])
{
    Image image = Image_alloc(500, 500);

    render(&image);

    write_to_tiff("test1.tiff", &image);

    Image_free(&image);

    return EXIT_SUCCESS;
}

#pragma once

#include <stdint.h>
#include <stddef.h>
//#include <assert.h>
//#include <stdlib.h>

#define sizeof_member(type, member) sizeof(((type *)0)->member)

enum {RED = 0, GREEN, BLUE, SAMPLES_PER_PIXEL = 3};

#pragma pack(push,1)
typedef struct Pixel
{
    uint8_t clr[SAMPLES_PER_PIXEL];
}
__attribute__ ((__packed__)) Pixel;
#pragma pack(pop)

typedef struct Image
{
    size_t xres;
    size_t yres;

    Pixel* pixels;
}
Image;

static inline
Pixel* Image_row(const Image* image, size_t row) {
    return (image->pixels + row*image->xres);
}

Image
Image_alloc(size_t x, size_t y);

void
Image_free(Image* image);


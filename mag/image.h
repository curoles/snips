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

static inline uint8_t Pixel_red(Pixel* p)   { return p->clr[RED]; }
static inline uint8_t Pixel_green(Pixel* p) { return p->clr[GREEN]; }
static inline uint8_t Pixel_blue(Pixel* p)  { return p->clr[BLUE]; }

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

static inline
Pixel* Image_at(const Image* image, size_t x, size_t y) {
    return (image->pixels + y*image->xres + x);
}

Image
Image_alloc(size_t x, size_t y);

void
Image_free(Image* image);

static inline
void
Image_set(Image* image, int x, int y, Pixel* clr) {
    *(Image_at(image, x, y)) = *clr;
}

static inline
void
Image_setSafe(Image* image, int x, int y, Pixel* clr) {
    if (0 <= x && x < image->xres && 0 <= y && y < image->yres) {
        *(Image_at(image, x, y)) = *clr;
    }
}


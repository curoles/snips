//https://github.com/jameswmccarty/Fractal-Flame-Algorithm-in-C/blob/master/fractal.c
//Ubuntu 17.04: sudo apt-get install libtiff-dev
//
// check https://github.com/crapp/geomandel
//
//
#include "write_to_tiff.h"

//#include <stdint.h>
//#include <stddef.h>
#include <assert.h>
//#include <stdlib.h>
#include <tiffio.h>

#include "image.h"

static
void write_tiff_tags(
    TIFF* tiff,
    const Image* image
)
{
    TIFFSetField (tiff, TIFFTAG_IMAGEWIDTH,      image->xres);
    TIFFSetField (tiff, TIFFTAG_IMAGELENGTH,     image->yres);
    TIFFSetField (tiff, TIFFTAG_ORIENTATION,     ORIENTATION_TOPLEFT);
    TIFFSetField (tiff, TIFFTAG_COMPRESSION,     COMPRESSION_DEFLATE);
    TIFFSetField (tiff, TIFFTAG_PLANARCONFIG,    PLANARCONFIG_CONTIG);
    TIFFSetField (tiff, TIFFTAG_PHOTOMETRIC,     PHOTOMETRIC_RGB);
    TIFFSetField (tiff, TIFFTAG_BITSPERSAMPLE,   8*sizeof_member(Pixel, clr[0]));
    TIFFSetField (tiff, TIFFTAG_SAMPLESPERPIXEL, sizeof_member(Pixel, clr)/sizeof_member(Pixel, clr[0]));

    //assert(SAMPLES_PER_PIXEL == sizeof_member(Pixel, clr)/sizeof_member(Pixel, clr[0]));
}

static
int
write_tiff(
    TIFF* tiff,
    const Image* image
)
{
    for (size_t row = 0; row < image->yres; row++)
    {
        if (TIFFWriteScanline(tiff, Image_row(image, row), row, 0) != 1)
	{
	    fprintf(stderr, "Could not write image\n");
	    return -1;
	}
    }

    return image->yres;
}

int
write_to_tiff(
    const char* filename,
    const Image* image
)
{
    assert(filename != NULL && image != NULL);

    TIFF* tiff;

    /* Open the output image */
    if ((tiff = TIFFOpen(filename, "w")) == NULL) {
        fprintf(stderr, "Could not open output image file %s.\n", filename);
        return -1;
    }

    /* Write the tiff tags to the file */
    write_tiff_tags(tiff, image);

    write_tiff(tiff, image);

    /* close the file */
    TIFFClose(tiff);

    return 0;
}


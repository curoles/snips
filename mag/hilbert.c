//http://www.donrelyea.com/hilbert_algorithmic_art_menu.htm
//http://mathworld.wolfram.com/HilbertCurve.html
//http://www.fundza.com/algorithmic/space_filling/hilbert/basics/index.html
//
//
//

/* x and y are the coordinates of the bottom left corner */
/* xi & xj are the i & j components of the unit x vector of this frame */
/* similarly yis and yjs */

void hilbert(
    int x,  int y,
    int xi, int xj,
    int yi, int yj,
    size_t n
)
{
    if (n <= 0) {
        LineTo(x + (xi + yi)/2, y + (xj + yj)/2);
    }
    else {
        hilbert(x,           y,           yi/2, yj/2,  xi/2,  xj/2, n-1);
        hilbert(x+xi/2,      y+xj/2 ,     xi/2, xj/2,  yi/2,  yj/2, n-1);
        hilbert(x+xi/2+yi/2, y+xj/2+yj/2, xi/2, xj/2,  yi/2,  yj/2, n-1);
        hilbert(x+xi/2+yi,   y+xj/2+yj,  -yi/2,-yj/2, -xi/2, -xj/2, n-1);
    }
}

/* Sample call */
//hilbert(0, 0, 300, 0, 0, 300, 4);

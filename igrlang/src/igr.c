#include <stdio.h>

#include "igr.h"
#include "selfcheck.h"
#include "print.h"


int main(int argc, const char* argv[])
{
    enable_print_colors(true);

    if (!selfcheck()) {
        printf("Self checking test %sFAILED%s\n",
            prtclr(PCLR_BOLD_RED), prtclr(PCLR_NONE));
        return FAIL;
    }
    return SUCCESS;
}

/*
//http://bisqwit.iki.fi/story/howto/openmp/

void test_opm()
{
int MAX_NUM=100,i,j,k;
#pragma omp parallel for default(shared) private(i, j, k)
for (i = 0; i < MAX_NUM; i++) {
     for (j = 0; j < MAX_NUM; j++) {
          for (k = 0; k < MAX_NUM; k++)
              ; //Y[i][j] += A[i][k] * B[k][j];
      }
}
}*/

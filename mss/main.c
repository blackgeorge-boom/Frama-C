/*
 * Maximum segment sum test
 * Takuo Watanabe (Tokyo Institute of Technology)
 */

#include <stdio.h>
#include <stdlib.h>

int mss (int *, int);

#define ALEN(a) (sizeof(a) / sizeof(a[0]))

void mss_test (int a[], int n) {
    printf("mss = %d\n", mss(a, n));
}

int main (int argc, char *argv[]) {
    int a1[] = { 31, -41, 59, 26, -53, 58, 97, -93, -23, 84 };
    mss_test(a1, ALEN(a1));
    return EXIT_SUCCESS;
}

/*
 * Maximum segment sum: a naive O(n^3) implementation
 * Takuo Watanabe (Tokyo Institute of Technology)
 *
 * To verify this file using Frama-C:
 *   frama-c -jessie mss.c
 *   frama-c -jessie -jessie-atp=ergo mss.c
 *
 */

#ifndef NO_JESSIE_PRAGMAS
#pragma JessieIntegerModel(math)
#endif

#include "max.h"
#include "mss.h"

/*@ requires i <= j && \valid_range(a, i, j);
  @ ensures \result == ssum(a, i, j);
  @*/
int sum (int a[], int i, int j) {
    int s = 0;
    int k;
    /*@ loop invariant i <= k <= j + 1 &&
      @                s == ssum(a, i, k - 1);
      @ loop variant j - k;
      @*/
    for (k = i; k <= j; k++)
        s += a[k];
    return s;
}

int mss (int a[], int n) {
    int i, j;
    int s = a[0];
    /*@ loop invariant 0 <= i < n + 1;
      @ loop variant n - i;
      @*/
    for (i = 0; i < n; i++) {
        /*@ loop invariant i <= j < n + 1;
          @ loop variant n - j;
          @*/
        for (j = i; j < n; j++) {
            s = max(s, sum(a, i, j));
        }
    }
    return s;
}

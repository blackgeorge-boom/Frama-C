/*
 * Maximum segment sum: O(n^3) implementation
 * Takuo Watanabe (Tokyo Institute of Technology)
 *
 * To verify this file using Frama-C:
 *   frama-c -jessie mss.c
 *   frama-c -jessie -jessie-atp=ergo mss.c
 *
 * This file can be successfully verified using the following configuration.
 *   Frama-C Carbon-20110201
 *   Alt-Ergo 0.92.2 / Simplify 1.5.7
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
    /*@ loop invariant i <= k <= j + 1 && s == ssum(a, i, k - 1);
      @ loop variant j - k;
      @*/
    for (int k = i; k <= j; k++)
        s += a[k];
    return s;
}

int mss (int a[], int n) {
    int s = a[0];
    //@ ghost int p = 0, q = 0;
    /*@ loop invariant 0 <= i <= n;
      @ loop invariant \forall integer k, l;
      @                0 <= k < i && k <= l < n ==> s >= ssum(a, k, l);
      @ loop invariant 0 <= p <= q < n && s == ssum(a, p, q);
      @ loop variant n - i;
      @*/
    for (int i = 0; i < n; i++) {
        /*@ loop invariant i <= j <= n;
          @ loop invariant \forall integer k, l;
          @                0 <= k < i && k <= l < n ==> s >= ssum(a, k, l);
          @ loop invariant \forall integer k;
          @                i <= k < j ==> s >= ssum(a, i, k);
          @ loop invariant 0 <= p <= q < n && s == ssum(a, p, q);
          @ loop variant n - j;
          @*/
        for (int j = i; j < n; j++) {
            //@ ghost if (s < sum(a, i, j)) { p = i; q = j; }
            s = max(s, sum(a, i, j));
        }
    }
    return s;
}

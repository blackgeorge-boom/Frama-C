/*
 * Maximum segment sum: O(n^2) implementation
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
        int t = 0;
        /*@ loop invariant i <= j <= n;
          @ loop invariant \forall integer k, l;
          @                0 <= k < i && k <= l < n ==> s >= ssum(a, k, l);
          @ loop invariant \forall integer k;
          @                i <= k < j ==> s >= ssum(a, i, k);
          @ loop invariant t == ssum(a, i, j - 1);
          @ loop invariant 0 <= p <= q < n && s == ssum(a, p, q);
          @ loop variant n - j;
          @*/
        for (int j = i; j < n; j++) {
            t = t + a[j];
            //@ ghost if (s < t) { p = i; q = j; }
            s = max(s, t);
        }
    }
    return s;
}

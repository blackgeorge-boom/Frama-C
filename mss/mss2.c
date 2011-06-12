/*
 * Maximum segment sum: O(n^2) implementation
 * Takuo Watanabe (Tokyo Institute of Technology)
 *
 * This file can be successfully verified using Frama-C with Jessie plugin.
 *   Frama-C Carbon-20110201
 *   Alt-Ergo 0.92.2 / Simplify 1.5.7 / CVC3 2.2
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
      @                0 <= k < i && k <= l < n ==> s >= segsum(a, k, l);
      @ loop invariant 0 <= p <= q < n && s == segsum(a, p, q);
      @ loop variant n - i;
      @*/
    for (int i = 0; i < n; i++) {
        int t = 0;
        /*@ loop invariant i <= j <= n;
          @ loop invariant \forall integer k, l;
          @                0 <= k < i && k <= l < n ==> s >= segsum(a, k, l);
          @ loop invariant \forall integer k;
          @                i <= k < j ==> s >= segsum(a, i, k);
          @ loop invariant t == segsum(a, i, j - 1);
          @ loop invariant 0 <= p <= q < n && s == segsum(a, p, q);
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

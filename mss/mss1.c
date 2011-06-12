/* 
 * Maximum segment sum: clever O(n) implementation
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
    int t = a[0], s = a[0];
    //@ ghost int p = 0, q = 0, r = 0;
    /*@ loop invariant 0 < k <= n;
      @ loop invariant \forall integer i;
      @                0 <= i < k  ==> t >= segsum(a, i, k - 1);
      @ loop invariant 0 <= p < k && t == segsum(a, p, k - 1);
      @ loop invariant \forall integer i, j;
      @                0 <= i <= j < k ==> s >= segsum(a, i, j);
      @ loop invariant 0 <= q <= r < k && s == segsum(a, q, r);
      @ loop variant n - k;
      @*/
    for (int k = 1; k < n; k++) {
        //@ ghost if (t < 0) p = k;
        t = max(t + a[k], a[k]);
        //@ ghost if (s < t) { q = p; r = k; }
        s = max(s, t);
    }
    return s;
}

/*
 * Maximum segment sum in linear time
 * Takuo Watanabe (Tokyo Institute of Technology)
 *
 * To verify this file using Frama-C:
 *   frama-c -jessie mss.c
 *   frama-c -jessie -jessie-atp=ergo mss.c
 *
 * This file can be successfully verified using the following configuration.
 *   Frama-C Carbon-20110201
 *   Alt-Ergo 0.92.2
 */

#ifdef JESSIE_PRAGMAS
#pragma JessieIntegerModel(math)
#endif

/*@ axiomatic Sum {
  @   logic integer sum{L}(int *a, integer i, integer j);
  @   axiom sum_0: \forall int *a, integer i, j; i > j ==> sum(a, i, j) == 0;
  @   axiom sum_n: \forall int *a, integer i, j; i <= j ==>
  @         sum(a, i, j) == sum(a, i, j - 1) + a[j];
  @ }
  @*/

//@ ensures \result == ((x >= y) ? x : y);
int max (int x, int y) {
    return (x >= y) ? x : y;
}

/*@ requires
  @   n > 0 &&
  @   \valid_range(a, 0, n - 1);
  @ ensures
  @   (\forall integer i, j; 0 <= i <= j < n ==> \result >= sum(a, i, j)) &&
  @   (\exists integer i, j; 0 <= i <= j < n && \result == sum(a, i, j));
  @*/
int mss (int a[], int n) {
    int t = a[0], s = a[0];
    //@ ghost int p = 0, q = 0, r = 0;
    /*@ loop invariant
      @      0 < k <= n &&
      @      0 <= p < k &&
      @      t == sum(a, p, k - 1) &&
      @      (\forall integer i; 0 <= i < k ==> t >= sum(a, i, k - 1)) &&
      @      0 <= q <= r < k &&
      @      s == sum(a, q, r) &&
      @      (\forall integer i, j; 0 <= i <= j < k ==> s >= sum(a, i, j));
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

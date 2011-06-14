#pragma JessieIntegerModel(math)

/*@ lemma hoge: \forall integer x, y; 
  @             x <= y ==> x <= (x + y) / 2 <= y;
  @*/

/*@ predicate Sorted(int *a, integer l, integer h) =
  @   \forall integer i, j; l <= i <= j <= h ==> a[i] <= a[j];
  @*/

/*@ requires \valid_range(a, lo, hi);
  @ requires Sorted(a, lo, hi);
  @ decreases hi - lo;
  @ assigns \nothing;
  @ behavior success:
  @   assumes \exists integer i; lo <= i <= hi && a[i] == v;
  @   ensures lo <= \result <= hi && a[\result] == v;
  @ behavior failure:
  @   assumes \forall integer i; lo <= i <= hi ==> a[i] != v;
  @   ensures \result == fv;
  @*/
int search1_rec (int a[], int lo, int hi, int v, int fv) {
    if (lo <= hi) {
        int m = (lo + hi) / 2;
        if (v == a[m])
            return m;
        else if (v < a[m])
            return search1_rec(a, lo, m - 1, v, fv);
        else
            return search1_rec(a, m + 1, hi, v, fv);
    }
    else
        return fv;
}

/*@ requires n > 0 && \valid_range(a, 0, n - 1);
  @ requires Sorted(a, 0, n - 1);
  @ behavior success:
  @   assumes \exists integer i; 0 <= i < n && a[i] == v;
  @   ensures 0 <= \result < n && a[\result] == v;
  @ behavior failure:
  @   assumes \forall integer i; 0 <= i < n  ==> a[i] != v;
  @   ensures \result == -1;
  @*/
int search1 (int a[], int n, int v) {
    return search1_rec(a, 0, n - 1, v, -1);
}

/*@ requires n > 0 && \valid_range(a, 0, n - 1);
  @ requires Sorted(a, 0, n - 1);
  @ behavior success:
  @   assumes \exists integer i; 0 <= i < n && a[i] == v;
  @   ensures 0 <= \result < n && a[\result] == v;
  @ behavior failure:
  @   assumes \forall integer i; 0 <= i < n  ==> a[i] != v;
  @   ensures \result == -1;
  @*/
int search2 (int a[], int n, int v) {
    int lo = 0, hi = n - 1;
    /*@ loop invariant 0 <= lo <= hi + 1 && hi < n;
      @ loop invariant \forall integer k;
      @                0 <= k < n && a[k] == v ==> lo <= k <= hi;
      @ loop variant hi - lo;
      @*/
    while (lo <= hi) {
        int m = (lo + hi) / 2;
        if (v == a[m])
            return m;
        else if (v < a[m])
            hi = m - 1;
        else
            lo = m + 1;
    }
    return - 1;
}

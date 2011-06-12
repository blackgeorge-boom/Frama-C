/* 
 * Maximum segment sum: ACSL specification
 * Takuo Watanabe (Tokyo Institute of Technology)
 */

// segment sum
/*@ axiomatic Segsum {
  @ logic integer segsum{L}(int *a, integer i, integer j);
  @ axiom segsum_0: \forall int *a, integer i, j; i > j
  @               ==> segsum(a, i, j) == 0;
  @ axiom segsum_n: \forall int *a, integer i, j; i <= j
  @               ==> segsum(a, i, j) == segsum(a, i, j - 1) + a[j];
  @ }
  @*/

/*@ requires n > 0 && \valid_range(a, 0, n - 1);
  @ ensures \forall integer i, j;
  @         0 <= i <= j < n ==> \result >= segsum(a, i, j);
  @ ensures \exists integer i, j;
  @         0 <= i <= j < n && \result == segsum(a, i, j);
  @*/
int mss (int a[], int n);

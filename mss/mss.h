// segment sum
/*@ axiomatic Ssum {
  @   logic integer ssum{L}(int *a, integer i, integer j);
  @   axiom ssum_0: \forall int *a, integer i, j; i > j
  @         ==> ssum(a, i, j) == 0;
  @   axiom ssum_n: \forall int *a, integer i, j; i <= j
  @         ==> ssum(a, i, j) == ssum(a, i, j - 1) + a[j];
  @ }
  @*/

/*@ requires n > 0 && \valid_range(a, 0, n - 1);
  @ ensures \forall integer i, j;
  @         0 <= i <= j < n ==> \result >= ssum(a, i, j);
  @ ensures \exists integer i, j;
  @         0 <= i <= j < n && \result == ssum(a, i, j);
  @*/
int mss (int a[], int n);

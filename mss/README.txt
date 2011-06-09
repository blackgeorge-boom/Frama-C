Maximum Segment Sum Problem

A segment sum of an array is the sum of a continuous elements in the array.

  ssum(A, i, j) = A[i] + A[i + 1] + ... + A[j]

The maximum segment sum (MSS) of an array is the maximum of all segment
sums of the array.

  mss(A) = max{ ssum(A, i, j) |  0 <= i <= j < |A| }

Here we assume that |A| (the length of A) is greater than zero.

Example: mss([31, -41, 59, 26, -53, 58, 97, -93, -23, 84]) = 187


ACSL Specification

We use the following ACSL specification for functions calculating MSS
of integer arrays.

/*@ requires
  @   n > 0 &&
  @   \valid_range(a, 0, n - 1);
  @ ensures
  @   (\forall integer i, j; 0 <= i <= j < n ==> \result >= ssum(a, i, j)) &&
  @   (\exists integer i, j; 0 <= i <= j < n && \result == ssum(a, i, j));
  @*/
int mss (int a[], int n);


The file mss1.c provides a C implementation of famous O(n) algorithm.
To verify this, it may be possible to write the loop invariant as follows. 
This looks simpler and cleaner. But it is hard to verify the existential
clauses with automatic provers such as Alt-Ergo or Simplify. Instead,
we provide some ghost variables that track the indices for current maximums.

/*@ loop invariant
  @      0 < k <= n &&
  @      (\forall integer i; 0 <= i < k ==> t >= sum(a, i, k - 1)) &&
  @      (\exists integer i; 0 <= i < k && t == sum(a, i, k - 1)) &&
  @      (\forall integer i, j; 0 <= i <= j < k ==> s >= sum(a, i, j)) &&
  @      (\exists integer i, j; 0 <= i <= j < k && s == sum(a, i, j));
  @ loop variant n - k;
  @*/


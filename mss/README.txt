* Maximum Segment Sum Problem

A segment sum of an array is the sum of a contiguous elements in the
array.

  ssum(A, i, j) = A[i] + A[i + 1] + ... + A[j]

The maximum segment sum (MSS) of an array is the maximum of all
segment sums of the array.

  mss(A) = max{ ssum(A, i, j) |  0 <= i <= j < |A| }

Here we assume that |A| (the length of A) is greater than zero.

Example: mss([31, -41, 59, 26, -53, 58, 97, -93, -23, 84]) = 187


* ACSL Specification

You can find the specifications of functions in the header files.
They can be verified using Frama-C with Jessie plugin.

  frama-c -jessie mss1.c

The above command starts gWhy (Why in GUI mode).
You can specify a prover.

  frama-c -jessie -jessie-atp=ergo mss1.c

Or, you can use make command.

  make jessie_mss1
  make ergo_mss1


* On Loop Invariants

The file mss1.c provides a C implementation of famous O(n) algorithm.
To verify this, it may be possible to write the loop invariants as
follows.

/*@ loop invariant 0 < k <= n;
  @ loop invariant \forall integer i; 0 <= i < k ==> t >= sum(a, i, k - 1);
  @ loop invariant \exists integer i; 0 <= i < k && t == sum(a, i, k - 1);
  @ loop invariant \forall integer i, j;
  @                0 <= i <= j < k ==> s >= sum(a, i, j);
  @ loop invariant \exists integer i, j;
  @                0 <= i <= j < k && s == sum(a, i, j);
  @ loop variant n - k;
  @*/

The above invariant is much simpler and clearer than the one in mss.h.
However it is generally hard to verify invariants including
existential clauses with automatic provers such as Alt-Ergo or
Simplify.  So we provide ghost variables that keep track of the
indices for current maximums.

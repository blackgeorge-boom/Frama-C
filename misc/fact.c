#pragma JessieIntegerModel(math)

/*@ axiomatic Factorial {
  @ logic integer fact(integer n);
  @ axiom factorial_0: fact(0) == 1;
  @ axiom factorial_n: \forall integer n;
  @                    n > 0 ==> fact(n) == n * fact(n - 1);
  @ }
  @*/

/*@ requires n >= 0;
  @ decreases n;
  @ ensures \result == fact(n);
  @*/
int fact1 (int n) {
    if (n == 0)
        return 1;
    else
        return n * fact1(n - 1);
}

/*@ requires n >= 0;
  @ ensures \result == fact(n);
  @*/
int fact2 (int n) {
    int a = 1;
    /*@ loop invariant 0 < k <= n + 1;
      @ loop invariant a == fact(k - 1);
      @ loop variant n - k;
      @*/
    for (int k = 1; k <= n; k++)
        a = k * a;
     return a;
}

/*@ requires n >= 0;
  @ decreases n;
  @ ensures \result == fact(n) * a;
  @*/
int fact3i (int n, int a) {
    if (n == 0)
        return a;
    else
        return fact3i(n - 1, n * a);
}

/*@ requires n >= 0;
  @ ensures \result == fact(n);
  @*/
int fact3 (int n) {
    return fact3i(n, 1);
}

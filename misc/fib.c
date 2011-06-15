#pragma JessieIntegerModel(math)

/*@ axiomatic Fibonacci {
  @ logic integer fib(integer n);
  @ axiom fib_0: fib(0) == 0;
  @ axiom fib_1: fib(1) == 1;
  @ axiom fib_n: \forall integer n;
  @              n >= 2 ==> fib(n) == fib(n - 1) + fib(n - 2);
  @ }
  @*/

/*@ requires n >= 0;
  @ decreases n;
  @ ensures \result == fib(n);
  @*/
int fib1 (int n) {
    if (n == 0)
        return 0;
    else if (n == 1)
        return 1;
    else
        return fib1(n - 1) + fib1(n - 2);
}


/*@ requires n >= 0;
  @ ensures \result == fib(n);
  @*/
int fib2 (int n) {
    int a = 0, b = 1;
    /*@ loop invariant 0 <= k <= n;
      @ loop invariant a == fib(k) && b == fib(k + 1);
      @ loop variant n - k;
      @*/
    for (int k = 0; k < n; k++) {
        int t = a + b;
        //@ ghost int l = k + 2;
        //@ assert t == fib(l - 1) + fib(l - 2);
        a = b;
        b = t;
    }
    return a;
}

/*@ requires n >= 0;
  @ ensures \result == fib(n);
  @*/
int fib3 (int n) {
    int a = 1, b = 0;
    /*@ loop invariant 0 <= k <= n;
      @ loop invariant k == 0 ==> a == 1; // == fib(-1)
      @ loop invariant k > 0 ==> a == fib(k - 1);
      @ loop invariant b == fib(k);
      @ loop variant n - k;
      @*/
    for (int k = 0; k < n; k++) {
        int t = a + b;
        //@ assert k == 0 ==> t == 1;
        //@ ghost int l = k + 1;
        //@ assert k > 0 ==> t == fib(l - 2) + fib(l - 1);
        a = b;
        b = t;
    }
    return b;
}

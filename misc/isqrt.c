#pragma JessieIntegerModel(math)

/*@ requires x >= 0;
  @ ensures \result >= 0;
  @ ensures \result * \result <= x;
  @ ensures (\result + 1) * (\result + 1) > x;
  @*/
int isqrt (int x) {
    int r = 1;
    /*@ loop invariant r >= 0;
      @ loop invariant (r - 1) * (r - 1) <= x;
      @ loop variant x - r * r;
      @*/
    while (r * r <= x)
        r++;
    return r - 1;
}

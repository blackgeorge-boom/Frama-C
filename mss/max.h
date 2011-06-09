/*@ behavior x_ge_y:
  @   assumes x >= y;
  @   ensures \result == x;
  @ behavior x_lt_y:
  @   assumes x < y;
  @   ensures \result == y;
  @*/
int max (int x, int y);

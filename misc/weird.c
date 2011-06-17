/*
 * A Weird Equilibrium
 */

/*@ predicate IsMax(integer m, integer x, integer y, integer z) =
  @   (x <= m && y <= m && z <= m) &&
  @   (x == m || y == m || z == m);
  @*/

/*@ ensures IsMax(\result, x, y, z);
  @*/
int weired_max (int x, int y, int z) {
    /*@ ghost int m = x > y ? x : y;
      @ m = z > m ? z : m;
      @*/
    /*@ loop invariant IsMax(m, x, y, z);
      @ loop variant 3 * m - (x + y + z);
      */
    while (1) {
        if (x < y) x++;
        else if (y < z) y++;
        else if (z < x) z++;
        else break;
    }
    //@ assert x == y == z;
    return x;
}


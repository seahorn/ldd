#include "util.h"
#include "cudd.h"
#include "tdd.h"
#include "tdd-ddd.h"


#include <stdio.h>

DdManager *cudd;
tdd_manager *tdd;
theory_t *t;


#define T(c,n) t->create_linterm ((c),(n))
#define C(n) t->create_int_cst(n)
#define CONS(tm,n,c) t->create_cons (T(tm,n),0,C(c))
  

void test0 ()
{
  /*  1 <= x <= 3 ==   (x-z <= 3) && (z-x <= -1)
      1 <= x <= 5 ==   (x-z <= 5) && (z-x <= -1)

      0 <= x <= 3 ==   (x-z <= 3) && (z-x <= 0)
  */


  /* variable ordering:
   * 0:z, 1:x, 2:y 
   * z is used as a special ZERO variable
   */

  int xMz[3] = {-1, 1, 0};
  int zMx[3] = {1, -1, 0};
  
  lincons_t l1, l2, l3, l4;
  
  tdd_node *d1, *d2, *d3, *d4;

  tdd_node *box1, *box2, *box3, *box4, *box5;

  l1 = CONS(xMz, 3, 3);
  d1 = to_tdd (tdd, l1);
  Cudd_Ref (d1);  
  Cudd_PrintMinterm (cudd, d1);
  
  l2 = CONS(zMx, 3, -1);
  d2 = to_tdd(tdd, l2);
  Cudd_Ref (d2);
  Cudd_PrintMinterm (cudd, d2);

  l3 = CONS (xMz, 3, 5);
  d3 = to_tdd(tdd, l3);
  Cudd_Ref (d3);  
  Cudd_PrintMinterm (cudd, d3);


  l4 = CONS (zMx, 3, 0);
  d4 = to_tdd(tdd, l4);
  Cudd_Ref (d4);
  Cudd_PrintMinterm (cudd, d4);

  box1 = tdd_and (tdd, d1, d2);
  Cudd_Ref (box1);
  
  box2 = tdd_and (tdd, d3, d2);
  Cudd_Ref (box2);
  
  box3 = tdd_box_extrapolate (tdd, box1, box2);
  Cudd_Ref (box3);

  box4 = tdd_and (tdd, d1, d4);
  Cudd_Ref (box4);
  
  box5 = tdd_box_extrapolate (tdd, box1, box4);
  Cudd_Ref (box5);

  Cudd_PrintMinterm (cudd, d1);
  Cudd_PrintMinterm (cudd, d2);
  Cudd_PrintMinterm (cudd, d3);
  Cudd_PrintMinterm (cudd, d4);
  Cudd_PrintMinterm (cudd, box1);
  Cudd_PrintMinterm (cudd, box2);
  Cudd_PrintMinterm (cudd, box3);


  assert (box3 == d2);
  assert (box5 == d1);
}


int main(void)
{
  cudd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);
  t = ddd_create_int_theory (3);
  tdd = tdd_init (cudd, t);
  test0 ();  

  return 0;
}

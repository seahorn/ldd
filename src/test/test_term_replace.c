#include "util.h"
#include "cudd.h"
#include "ldd.h"
#include "tvpi.h"

#include <stdio.h>

DdManager *cudd;
LddManager *ldd;
theory_t *t;


#define T(c,n) t->create_linterm ((c),(n))
#define C(n) t->create_int_cst(n)
#define CONS(tm,n,c) t->create_cons (T(tm,n),0,C(c))
  

void test0 ()
{

  /*
     1 <= x <= 3 && 2 <= y <= 3
     do  x <- y
     expect: 2 <= x <= 3 && 2 <= y <= 3 */
  


  /* variable ordering:
   * 0:z, 1:x, 2:y 
   * z is used as a special ZERO variable
   */

  constant_t k1, k2;
  
  int xMz[3] = {-1, 1, 0};
  int zMx[3] = {1, -1, 0};
  int yMz[3] = {-1, 0, 1};
  int zMy[3] = {1, 0, -1};
  
  
  lincons_t l1, l2, l3, l4, l5;
  LddNode *d1, *d2, *d3, *d4, *d5;

  LddNode *box1, *box2, *box3, *box4, *box5, *box6;

  /* x <= 3 */
  l1 = CONS(xMz, 3, 3);
  d1 = Ldd_FromCons (ldd, l1);
  Ldd_Ref (d1);  
  
  /* 1 <= x */
  l2 = CONS(zMx, 3, -1);
  d2 = Ldd_FromCons(ldd, l2);
  Ldd_Ref (d2);

  /* 2 <= x */
  l3 = CONS(zMx, 3, -2);
  d3 = Ldd_FromCons(ldd, l3);
  Ldd_Ref (d3);

  /* y <= 5 */
  l4 = CONS(yMz, 3, 3);
  d4 = Ldd_FromCons (ldd, l4);
  Ldd_Ref (d4);  

  /* 2 <= y */
  l5 = CONS(zMy, 3, -2);
  d5 = Ldd_FromCons(ldd, l5);
  Ldd_Ref (d5);


  /* 1 <= x < = 3 */
  box1 = Ldd_And (ldd, d1, d2);
  Ldd_Ref (box1);
  
  /* 2 <= y <= 3 */
  box2 = Ldd_And (ldd, d4, d5);
  Ldd_Ref (box2);
  
  /* 1 <= x <= 3 && 2 <= y <= 5 */
  box3 = Ldd_And (ldd, box1, box2);
  Ldd_Ref (box3);

  k1 = C(1);
  k2 = C(0);

  box4 = Ldd_TermReplace (ldd, box3, 
			   t->get_term (l2), t->get_term (l5),
			   k1, k2, k2);
  Ldd_Ref (box4);

  t->destroy_cst (k1); k1 = NULL;
  t->destroy_cst (k2); k2 = NULL;

  /* 2 <= x <= 3 */
  box5 = Ldd_And (ldd, d1, d3);
  Ldd_Ref (box5);
  
  box6 = Ldd_And (ldd, box5, box2);
  Ldd_Ref (box6);

  
  Ldd_PrintMinterm (ldd, box3);
  printf ("\n");
  
  Ldd_PrintMinterm (ldd, box4);
  printf ("\n");
  Ldd_PrintMinterm (ldd, box6);
  
  assert (box6 == box4);
  printf ("SUCCESS\n");

}

int t_type = 2;

int main(int argc, char** argv)
{
  
  if (argc > 1)
    if (argv[1][0] == 't')
      t_type = 2;
  
  
  cudd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);
  if (t_type == 2)
    t = tvpi_create_theory (3);
  ldd = Ldd_Init (cudd, t);
  test0 ();  

  return 0;
}

#include "util.h"
#include "cudd.h"
#include "tdd.h"
/* #include "tdd-ddd.h" */
#include "box.h"
#include "tvpi.h"


#include <stdio.h>

DdManager *cudd;
LddManager *tdd;
theory_t *t;


#define T(c,n) t->create_linterm ((c),(n))
#define C(n) t->create_int_cst(n)
#define CONS(tm,n,c) t->create_cons (T(tm,n),0,C(c))
  


void and_accum (LddNode **r, LddNode *n)
{
  /* compute: r <- r && n */
  LddNode *tmp;

  tmp = Ldd_And (tdd, *r, n);
  Ldd_Ref (tmp);

  Ldd_RecursiveDeref (tdd, *r); 
  *r = tmp;
}


void test1 ()
{
  int x2[4] = {0,1,0,0};
  int x3[4] = {0,0,1,0};
  int x7[4] = {0,0,0,1};


  LddNode *d[5];

  LddNode *r1, *r2, *r3, *r4;

  int i = 0;

  
  fprintf (stdout, "\n\nTEST 1\n");
  
  /* 0: x2 <= -1 */
  d[i] = to_tdd (tdd, CONS (x2,4,-1));
  Ldd_Ref (d[i++]);

  /* 1: x2 <= 1 */
  d[i] = to_tdd (tdd, CONS (x2,4,1));
  Ldd_Ref (d[i++]);

  /* 2: x3 <= 0 */
  d[i] = to_tdd (tdd, CONS (x3,4,0));
  Ldd_Ref (d[i++]);

  /* 3: x7 <= 0 */
  d[i] = to_tdd (tdd, CONS (x7,4,0));
  Ldd_Ref (d[i++]);

  /* 4: x2 <= 4 */
  d[i] = to_tdd (tdd, CONS (x2,4,4));
  Ldd_Ref (d[i++]);


  r1 = Ldd_And (tdd, Cudd_Not(d[0]), d[1]);
  Ldd_Ref(r1);

  and_accum (&r1, Cudd_Not(d[2]));
  and_accum (&r1, Cudd_Not (d[3]));

  r2 = Ldd_And (tdd, Cudd_Not (d[1]), d[4]);
  Ldd_Ref (r2);
  
  and_accum (&r2, Cudd_Not (d[2]));
  and_accum (&r2, d[3]);

  Ldd_PrintMinterm (tdd, r1);
  Ldd_PrintMinterm (tdd, r2);

  r3 = Ldd_Or (tdd, r1, r2);
  Ldd_Ref (r3);

  printf ("r3\n");
  Ldd_PrintMinterm (tdd, r3);



  r4 = Ldd_TermMinmaxApprox (tdd, r3);
  Ldd_Ref (r4);


  printf ("r4\n");
  Ldd_PrintMinterm (tdd, r4);
  
 

  {
    LddNode *a;
    
    a = Ldd_And (tdd, Cudd_Not (d[0]), d[4]);
    Ldd_Ref (a);
    and_accum (&a, Cudd_Not (d[2]));

    assert (a == r4);
    
  }
  

}
void test0 ()
{
  /*  1 <= x <= 3 ==   (x <= 3) && (-x <= -1)
      1 <= x <= 5 ==   (x <= 5) && (-x <= -1)
      0 <= x <= 3 ==   (x <= 3) && (-x <= 0)
  */


  /* variable ordering:
   * 0:z, 1:x, 2:y 
   */

  int x[3] = {0, 1, 0};
  int nx[3] = {0, -1, 0};
  
  lincons_t l1, l2, l3, l4;
  
  LddNode *d1, *d2, *d3, *d4;

  LddNode *box1, *box2, *box3, *box4, *box5;
  
  fprintf (stdout, "\n\nTEST 0\n");


  l1 = CONS(x, 3, 3);
  d1 = to_tdd (tdd, l1);
  Cudd_Ref (d1);  
  /* Cudd_PrintMinterm (cudd, d1);*/
  Ldd_PrintMinterm (tdd, d1);
  
  l2 = CONS(nx, 3, -1);
  d2 = to_tdd(tdd, l2);
  Cudd_Ref (d2);
  Ldd_PrintMinterm (tdd, d2);

  l3 = CONS (x, 3, 5);
  d3 = to_tdd(tdd, l3);
  Cudd_Ref (d3);  
  Ldd_PrintMinterm (tdd, d3);


  l4 = CONS (nx, 3, 0);
  d4 = to_tdd(tdd, l4);
  Cudd_Ref (d4);
  Ldd_PrintMinterm (tdd, d4);

  box1 = Ldd_And (tdd, d1, d2);
  Cudd_Ref (box1);
  
  box2 = Ldd_And (tdd, d3, d2);
  Cudd_Ref (box2);
  
  box3 = Ldd_BoxExtrapolate (tdd, box1, box2);
  Cudd_Ref (box3);

  box4 = Ldd_And (tdd, d1, d4);
  Cudd_Ref (box4);
  
  box5 = Ldd_BoxExtrapolate (tdd, box1, box4);
  Cudd_Ref (box5);


  printf ("d1\n");
  Ldd_PrintMinterm (tdd, d1);
  Cudd_PrintMinterm (cudd, d1);
  printf ("d2\n");
  Ldd_PrintMinterm (tdd, d2);
  Cudd_PrintMinterm (cudd, d2);
  printf ("d3\n");
  Ldd_PrintMinterm (tdd, d3);
  Cudd_PrintMinterm (cudd, d3);
  printf ("d4\n");
  Ldd_PrintMinterm (tdd, d4);
  Cudd_PrintMinterm (cudd, d4);
  printf ("box1\n");
  Ldd_PrintMinterm (tdd, box1);
  Cudd_PrintMinterm (cudd, box1);
  printf ("box2\n");
  Ldd_PrintMinterm (tdd, box2);
  Cudd_PrintMinterm (cudd, box2);
  printf ("box3\n");
  Ldd_PrintMinterm (tdd, box3);


  assert (box3 == d2);
  assert (box5 == d1);

  Ldd_ManagerDebugDump (tdd);
  
}

void test2()
{
  int x[3] = {0, 1, 0};

  lincons_t l1;
  
  LddNode *d1, *d2, *d3;

  
  fprintf (stdout, "\n\nTEST 2\n");


  l1 = CONS(x, 3, 3);
  d1 = to_tdd (tdd, l1);
  Cudd_Ref (d1);  

  d2 = to_tdd (tdd, l1);
  Cudd_Ref (d2);
  
  assert (d1 == d2);

  d3 = to_tdd (tdd, l1);
  assert (d2 == d3);

  Ldd_ManagerDebugDump (tdd);
}

int t_type = 4;

int main(int argc, char** argv)
{

  if (argc > 1)
    if (argv[1][0] == 't')
      t_type = 2;

  
  cudd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);  
  if (t_type == 2)
    t = tvpi_create_theory (4);
  else
    t = box_create_theory (4);
  tdd = Ldd_Init (cudd, t);
  test0 ();
  test1 ();  
  test2 ();
  return 0;
}

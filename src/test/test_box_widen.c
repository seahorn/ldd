#include "util.h"
#include "cudd.h"
#include "tdd.h"
/* #include "tdd-ddd.h" */
#include "box.h"


#include <stdio.h>

DdManager *cudd;
tdd_manager *tdd;
theory_t *t;


#define T(c,n) t->create_linterm ((c),(n))
#define C(n) t->create_int_cst(n)
#define CONS(tm,n,c) t->create_cons (T(tm,n),0,C(c))
  


void and_accum (tdd_node **r, tdd_node *n)
{
  /* compute: r <- r && n */
  tdd_node *tmp;

  tmp = tdd_and (tdd, *r, n);
  tdd_ref (tmp);

  tdd_recursiveDeref (tdd, *r); 
  *r = tmp;
}


void test1 ()
{
  int x2[4] = {0,1,0,0};
  int x3[4] = {0,0,1,0};
  int x7[4] = {0,0,0,1};


  tdd_node *d[5];

  tdd_node *r1, *r2, *r3, *r4;

  int i = 0;

  
  fprintf (stdout, "\n\nTEST 1\n");
  
  /* 0: x2 <= -1 */
  d[i] = to_tdd (tdd, CONS (x2,4,-1));
  tdd_ref (d[i++]);

  /* 1: x2 <= 1 */
  d[i] = to_tdd (tdd, CONS (x2,4,1));
  tdd_ref (d[i++]);

  /* 2: x3 <= 0 */
  d[i] = to_tdd (tdd, CONS (x3,4,0));
  tdd_ref (d[i++]);

  /* 3: x7 <= 0 */
  d[i] = to_tdd (tdd, CONS (x7,4,0));
  tdd_ref (d[i++]);

  /* 4: x2 <= 4 */
  d[i] = to_tdd (tdd, CONS (x2,4,4));
  tdd_ref (d[i++]);


  r1 = tdd_and (tdd, Cudd_Not(d[0]), d[1]);
  tdd_ref(r1);

  and_accum (&r1, Cudd_Not(d[2]));
  and_accum (&r1, Cudd_Not (d[3]));

  r2 = tdd_and (tdd, Cudd_Not (d[1]), d[4]);
  tdd_ref (r2);
  
  and_accum (&r2, Cudd_Not (d[2]));
  and_accum (&r2, d[3]);

  tdd_print_minterm (tdd, r1);
  tdd_print_minterm (tdd, r2);

  r3 = tdd_or (tdd, r1, r2);
  tdd_ref (r3);

  printf ("r3\n");
  tdd_print_minterm (tdd, r3);



  r4 = tdd_term_minmax_approx (tdd, r3);
  tdd_ref (r4);


  printf ("r4\n");
  tdd_print_minterm (tdd, r4);
  
 

  {
    tdd_node *a;
    
    a = tdd_and (tdd, Cudd_Not (d[0]), d[4]);
    tdd_ref (a);
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
  
  tdd_node *d1, *d2, *d3, *d4;

  tdd_node *box1, *box2, *box3, *box4, *box5;
  
  fprintf (stdout, "\n\nTEST 0\n");


  l1 = CONS(x, 3, 3);
  d1 = to_tdd (tdd, l1);
  Cudd_Ref (d1);  
  /* Cudd_PrintMinterm (cudd, d1);*/
  tdd_print_minterm (tdd, d1);
  
  l2 = CONS(nx, 3, -1);
  d2 = to_tdd(tdd, l2);
  Cudd_Ref (d2);
  tdd_print_minterm (tdd, d2);

  l3 = CONS (x, 3, 5);
  d3 = to_tdd(tdd, l3);
  Cudd_Ref (d3);  
  tdd_print_minterm (tdd, d3);


  l4 = CONS (nx, 3, 0);
  d4 = to_tdd(tdd, l4);
  Cudd_Ref (d4);
  tdd_print_minterm (tdd, d4);

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


  printf ("d1\n");
  tdd_print_minterm (tdd, d1);
  Cudd_PrintMinterm (cudd, d1);
  printf ("d2\n");
  tdd_print_minterm (tdd, d2);
  Cudd_PrintMinterm (cudd, d2);
  printf ("d3\n");
  tdd_print_minterm (tdd, d3);
  Cudd_PrintMinterm (cudd, d3);
  printf ("d4\n");
  tdd_print_minterm (tdd, d4);
  Cudd_PrintMinterm (cudd, d4);
  printf ("box1\n");
  tdd_print_minterm (tdd, box1);
  Cudd_PrintMinterm (cudd, box1);
  printf ("box2\n");
  tdd_print_minterm (tdd, box2);
  Cudd_PrintMinterm (cudd, box2);
  printf ("box3\n");
  tdd_print_minterm (tdd, box3);


  assert (box3 == d2);
  assert (box5 == d1);

  tdd_manager_debug_dump (tdd);
  
}

void test2()
{
  int x[3] = {0, 1, 0};
  int nx[3] = {0, -1, 0};
  
  lincons_t l1, l2, l3, l4;
  
  tdd_node *d1, *d2, *d3, *d4;

  tdd_node *box1, *box2, *box3, *box4, *box5;
  
  fprintf (stdout, "\n\nTEST 2\n");


  l1 = CONS(x, 3, 3);
  d1 = to_tdd (tdd, l1);
  Cudd_Ref (d1);  

  d2 = to_tdd (tdd, l1);
  Cudd_Ref (d2);
  
  assert (d1 == d2);

  d3 = to_tdd (tdd, l1);
  assert (d2 == d3);

  tdd_manager_debug_dump (tdd);
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
  tdd = tdd_init (cudd, t);
  test0 ();
  test1 ();  
  test2 ();
  return 0;
}

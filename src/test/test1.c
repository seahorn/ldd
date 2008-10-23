#include "util.h"
#include "cudd.h"
#include "tdd.h"
#include "tdd-ddd.h"


#include <stdio.h>

int main(void)
{
  
  DdManager *cudd;
  tdd_manager* tdd;
  theory_t * t;
  


  constant_t i5, i10, i15;
  int cf1[3] = {1, -1, 0};
  int cf2[3] = {0, 1, -1};
  int cf3[3] = {1, 0, -1};
  
  
  linterm_t t1, t2, t3;
  lincons_t l1, l2, l3;

  tdd_node *d1, *d2, *d3, *d4, *d5, *d6, *d7;

  printf ("Creating the world...\n");
  cudd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);
  t = ddd_create_int_theory (3);
  tdd = tdd_init (cudd, t);


  /* variable ordering:
   * 0:x, 1:y, 2:z */

  
  /* constants */
  i5 = t->create_int_cst (5);
  i10 = t->create_int_cst (10);
  i15 = t->create_int_cst (15);


  /*
    x-y <= 5 
   */
  t1 = t->create_linterm (cf1, 3);
  l1 = t->create_cons (t1, 0, i5);
  d1 = to_tdd (tdd, l1);
  Cudd_Ref (d1);

  printf ("d1 is:\n");
  Cudd_PrintMinterm (cudd, d1);
  
  /* 
     y-z <= 10
   */
  t2 = t->create_linterm (cf2, 3);
  l2 = t->create_cons (t2, 0, i10);
  d2 = to_tdd (tdd, l2);
  Cudd_Ref (d2);
  printf ("d2 is:\n");
  Cudd_PrintMinterm (cudd, d2);

  /* 
     x-z <= 15
   */
  t3 = t->create_linterm (cf3, 3);
  l3 = t->create_cons (t3, 0, i15);
  d3 = to_tdd (tdd, l3);
  Cudd_Ref (d3);
  printf ("d3 is:\n");
  Cudd_PrintMinterm (cudd, d3);
  
  
  d4 = tdd_and (tdd, d1, d2);
  Cudd_Ref (d4);
  printf ("d4 is:\n");
  Cudd_PrintMinterm (cudd, d4);

  d5 = tdd_or (tdd, d1, d2);
  Cudd_Ref (d5);
  printf ("d5 is:\n");
  Cudd_PrintMinterm (cudd, d5);
  
  /*
    x -y <=5 && y - z <= 10 => x-z <= 15
   */

  d6 = tdd_or (tdd, tdd_not (d4), d3);
  Cudd_Ref (d6);
  printf ("d6 is:\n");
  Cudd_PrintMinterm (cudd, d6);
  
  {
    d7 = tdd_univ_abstract (tdd, d6, 0);
    d7 = tdd_univ_abstract (tdd, d7, 1);
    d7 = tdd_univ_abstract (tdd, d7, 2);
    printf ("univ d7 is:\n");
    Cudd_PrintMinterm (cudd, d7);

    d7 = tdd_exist_abstract (tdd, d6, 0);
    d7 = tdd_exist_abstract (tdd, d7, 1);
    d7 = tdd_exist_abstract (tdd, d7, 2);
    printf ("exist d7 is:\n");
    Cudd_PrintMinterm (cudd, d7);
  }
      

  printf ("Destroying the world...\n");
  tdd_quit (tdd);
  ddd_destroy_theory (t);
  Cudd_Quit (cudd);
  
  return 0;
}

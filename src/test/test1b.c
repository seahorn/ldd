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
  

  constant_t ni5, ni10, ni15;
  int cf1[3] = {1, -1, 0};
  int cf2[3] = {-1, 1, 0};
  
  
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
  ni5 = t->create_int_cst (-5);
  ni10 = t->create_int_cst (-10);
  ni15 = t->create_int_cst (-15);



  
  /*
    x - y <= -10
   */
  t1 = t->create_linterm (cf1, 3);
  l1 = t->create_cons (t1, 0, ni10);
  d1 = to_tdd (tdd, l1);
  Cudd_Ref (d1);

  printf ("d1 is:\n");
  Cudd_PrintMinterm (cudd, d1);
  
  /* 
     y - x <= -5
   */
  t2 = t->create_linterm (cf2, 3);
  l2 = t->create_cons (t2, 0, ni5);
  d2 = to_tdd (tdd, l2);
  Cudd_Ref (d2);
  printf ("d2 is:\n");
  Cudd_PrintMinterm (cudd, d2);


  d3 = tdd_or (tdd, d1, d2);
  printf ("d3: d1 || d2 is:\n");
  Cudd_PrintMinterm (cudd, d3);
      

  printf ("Destroying the world...\n");
  tdd_quit (tdd);
  ddd_destroy_theory (t);
  Cudd_Quit (cudd);
  
  return 0;
}

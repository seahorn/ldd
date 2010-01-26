#include "util.h"
#include "cudd.h"
#include "tdd.h"
#include "tvpi.h"

#include <stdio.h>

int main(int argc, char** argv)
{
  
  DdManager *cudd;
  LddManager* tdd;
  theory_t * t;
  

  constant_t ni5, ni10, ni15;
  int cf1[3] = {1, -1, 0};
  int cf2[3] = {-1, 1, 0};
  
  
  linterm_t t1, t2;
  lincons_t l1, l2;

  LddNode *d1, *d2, *d3;


  /* 1 is DDD, 2 is TVPI */
  int t_type = 1;
  if (argc > 1)
    {
      if (argv [1][0] == 't')
	t_type = 2;
      else if (argv [1][0] == 'u')
	t_type = 5;
    }

  printf ("Creating the world...\n");
  cudd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);
  if (t_type == 2)
    t = tvpi_create_theory (3);
  else if (t_type == 5)
    t = tvpi_create_utvpiz_theory (3);
  tdd = Ldd_Init (cudd, t);


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
  Ldd_PrintMinterm (tdd, d1);
  
  /* 
     y - x <= -5
   */
  t2 = t->create_linterm (cf2, 3);
  l2 = t->create_cons (t2, 0, ni5);
  d2 = to_tdd (tdd, l2);
  Cudd_Ref (d2);
  printf ("d2 is:\n");
  Ldd_PrintMinterm (tdd, d2);


  d3 = Ldd_Or (tdd, d1, d2);
  printf ("d3: d1 || d2 is:\n");
  Ldd_PrintMinterm (tdd, d3);
      

  printf ("Destroying the world...\n");
  Ldd_Quit (tdd);
  if (t_type == 2 || t_type == 5)
    tvpi_destroy_theory (t);
  Cudd_Quit (cudd);
  
  return 0;
}

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
  


  constant_t i5, i10, i15;
  int cf1[3] = {1, -1, 0};
  int cf2[3] = {0, 1, -1};
  int cf3[3] = {1, 0, -1};
  
  
  linterm_t t1, t2, t3;
  lincons_t l1, l2, l3;

  LddNode *d1, *d2, *d3, *d4, *d5, *d6, *d7;


  /* 1 is DDD, 2 is TVPI , 5 is UTVPI(Z)*/
  int t_type = 2;
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
  i5 = t->create_int_cst (5);
  i10 = t->create_int_cst (10);
  i15 = t->create_int_cst (15);


  /*
    x-y <= 5 
   */
  t1 = t->create_linterm (cf1, 3);
  l1 = t->create_cons (t1, 0, i5);
  d1 = Ldd_FromCons (tdd, l1);
  Cudd_Ref (d1);

  printf ("d1 is:\n");
  Ldd_PrintMinterm (tdd, d1);
  
  /* 
     y-z <= 10
   */
  t2 = t->create_linterm (cf2, 3);
  l2 = t->create_cons (t2, 0, i10);
  d2 = Ldd_FromCons (tdd, l2);
  Cudd_Ref (d2);
  printf ("d2 is:\n");
  Ldd_PrintMinterm (tdd, d2);

  /* 
     x-z <= 15
   */
  t3 = t->create_linterm (cf3, 3);
  l3 = t->create_cons (t3, 0, i15);
  d3 = Ldd_FromCons (tdd, l3);
  Cudd_Ref (d3);
  printf ("d3 is:\n");
  Ldd_PrintMinterm (tdd, d3);
  
  
  d4 = Ldd_And (tdd, d1, d2);
  Cudd_Ref (d4);
  printf ("d4 is:\n");
  Ldd_PrintMinterm (tdd, d4);

  d5 = Ldd_Or (tdd, d1, d2);
  Cudd_Ref (d5);
  printf ("d5 is:\n");
  Ldd_PrintMinterm (tdd, d5);
  
  /*
    x -y <=5 && y - z <= 10 => x-z <= 15
   */

  d6 = Ldd_Or (tdd, Ldd_Not (d4), d3);
  Cudd_Ref (d6);
  printf ("d6 is:\n");
  Ldd_PrintMinterm (tdd, d6);
  
  {
    d7 = Ldd_UnivAbstract (tdd, d6, 0);
    d7 = Ldd_UnivAbstract (tdd, d7, 1);
    d7 = Ldd_UnivAbstract (tdd, d7, 2);
    printf ("univ d7 is:\n");
    Ldd_PrintMinterm (tdd, d7);

    d7 = Ldd_ExistAbstract (tdd, d6, 2);
    printf ("exist x2. d6 is:\n");
    Ldd_PrintMinterm (tdd, d7);
    d7 = Ldd_ExistAbstract (tdd, d7, 1);
    d7 = Ldd_ExistAbstract (tdd, d7, 0);
    printf ("exist d7 is:\n");
    Ldd_PrintMinterm (tdd, d7);

    d7 = Ldd_ExistsAbstractLW (tdd, d6, 2);
    printf ("existLW x2. d6 is:\n");
    Ldd_PrintMinterm (tdd, d7);
    d7 = Ldd_ExistsAbstractLW (tdd, d7, 1);
    d7 = Ldd_ExistsAbstractLW (tdd, d7, 0);
    printf ("exist LW d7 is:\n");
    Ldd_PrintMinterm (tdd, d7);
  }
      

  printf ("Destroying the world...\n");
  Ldd_Quit (tdd);
  if (t_type == 2 || t_type == 5)
    tvpi_destroy_theory (t);
  Cudd_Quit (cudd);
  
  return 0;
}

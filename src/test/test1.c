#include "util.h"
#include "cudd.h"
#include "ldd.h"
#include "tvpi.h"

#include <stdio.h>

int main(int argc, char** argv)
{
  
  DdManager *cudd;
  LddManager* ldd;
  theory_t * t;
  


  constant_t i5, i10, i15;
  int cf1[3] = {1, -1, 0};
  int cf2[3] = {0, 1, -1};
  int cf3[3] = {1, 0, -1};
  
  
  linterm_t t1, t2, t3;
  lincons_t l1, l2, l3;

  LddNode *d1, *d2, *d3, *d4, *d5, *d6, *d7;


  /* 2 is TVPI , 5 is UTVPI(Z)*/
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

  printf ("Creating the theory...\n");
  if (t_type == 2)
    t = tvpi_create_theory (3);
  else if (t_type == 5)
    t = tvpi_create_utvpiz_theory (3);

  /** initialize LDD */
  ldd = Ldd_Init (cudd, t);


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
  d1 = Ldd_FromCons (ldd, l1);
  Ldd_Ref (d1);

  printf ("d1 is:\n");
  Ldd_PrintMinterm (ldd, d1);
  
  /* 
     y-z <= 10
   */
  t2 = t->create_linterm (cf2, 3);
  l2 = t->create_cons (t2, 0, i10);
  d2 = Ldd_FromCons (ldd, l2);
  Ldd_Ref (d2);
  printf ("d2 is:\n");
  Ldd_PrintMinterm (ldd, d2);

  /* 
     x-z <= 15
   */
  t3 = t->create_linterm (cf3, 3);
  l3 = t->create_cons (t3, 0, i15);
  d3 = Ldd_FromCons (ldd, l3);
  Ldd_Ref (d3);
  printf ("d3 is:\n");
  Ldd_PrintMinterm (ldd, d3);
  
  
  d4 = Ldd_And (ldd, d1, d2);
  Ldd_Ref (d4);
  printf ("d4 is:\n");
  Ldd_PrintMinterm (ldd, d4);

  d5 = Ldd_Or (ldd, d1, d2);
  Ldd_Ref (d5);
  printf ("d5 is:\n");
  Ldd_PrintMinterm (ldd, d5);
  
  /*
    x -y <=5 && y - z <= 10 => x-z <= 15
   */

  d6 = Ldd_Or (ldd, Ldd_Not (d4), d3);
  Ldd_Ref (d6);
  printf ("d6 is:\n");
  Ldd_PrintMinterm (ldd, d6);


  /** Some quantification examples */
  {
    d7 = Ldd_UnivAbstract (ldd, d6, 0);
    d7 = Ldd_UnivAbstract (ldd, d7, 1);
    d7 = Ldd_UnivAbstract (ldd, d7, 2);
    printf ("univ d7 is:\n");
    Ldd_PrintMinterm (ldd, d7);

    d7 = Ldd_ExistsAbstract (ldd, d6, 2);
    printf ("exist x2. d6 is:\n");
    Ldd_PrintMinterm (ldd, d7);
    d7 = Ldd_ExistsAbstract (ldd, d7, 1);
    d7 = Ldd_ExistsAbstract (ldd, d7, 0);
    printf ("exist d7 is:\n");
    Ldd_PrintMinterm (ldd, d7);

    d7 = Ldd_ExistsAbstractLW (ldd, d6, 2);
    printf ("existLW x2. d6 is:\n");
    Ldd_PrintMinterm (ldd, d7);
    d7 = Ldd_ExistsAbstractLW (ldd, d7, 1);
    d7 = Ldd_ExistsAbstractLW (ldd, d7, 0);
    printf ("exist LW d7 is:\n");
    Ldd_PrintMinterm (ldd, d7);
  }


  /** exporting an LDD into SMT-LIB format */
  printf ("d6 in SMTLIB:\n");
  Ldd_DumpSmtLibV1 (ldd, d6, NULL, "d6", stdout);
  printf ("\n");
      

  {
    char* vnames [3] = {"x", "y", "z"  };
    printf ("d6 in SMTLIB (with var names) :\n");
    Ldd_DumpSmtLibV1 (ldd, d6, vnames, "d6", stdout);
    printf ("\n");
  }
  

  printf ("Destroying the world...\n");
  Ldd_Quit (ldd);
  if (t_type == 2 || t_type == 5)
    tvpi_destroy_theory (t);
  Cudd_Quit (cudd);
  
  return 0;
}

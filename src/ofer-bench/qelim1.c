#include <stdio.h>

#include "util.h"
#include "cudd.h"
#include "tdd.h"
#include "tdd-ddd.h"

extern void yyparse (void);

extern  DdManager *cudd;
extern  tdd_manager* tdd;
extern  theory_t *t;


extern int bench_max;
extern tdd_node* bench;

int main (int argc, char** argv)
{
  size_t size;
  int i;
  tdd_node* res;

  if (argc != 2)
    bench_max = 50;
  else
    bench_max = atoi (argv [1]);
  
  printf ("Benchmark with max_bench=%d\n", bench_max);

  //  yydebug = 1;
  yyparse ();
  printf ("Parsing ended with %p, of size %d\n", 
	  bench, Cudd_DagSize (bench));

  //tdd_manager_debug_dump (tdd);
  

  //t->theory_debug_dump (t);

  size = t->num_of_vars (t);
  printf ("Using %d DD variables\n", size);


/*   fprintf (stdout, "Enabling dynamic reordering\n"); */
/*   /\* default method is CUDD_REORDER_SIFT *\/ */
/*   Cudd_AutodynEnable (cudd, CUDD_REORDER_SAME); */

  printf ("Starting existential quantification\n");
  res = bench;

  //for (i = size - 1 ; i >= 0; i--)
  for (i = 1; i < size ; i++)
    {
      tdd_node* tmp;
      /* Only run quantification when needed */
      if (Cudd_IsConstant (res)) break;

      tmp = tdd_exist_abstract (tdd, res, i);
      Cudd_Ref (tmp);
      Cudd_RecursiveDeref (cudd, res);
      res = tmp;
      printf ("After quantifying x%d the size is %d\n",
	      i, Cudd_DagSize (res));
      //tdd_manager_debug_dump (tdd);

      /* 10 = whatever */
      Cudd_ReduceHeap (cudd, CUDD_REORDER_SIFT, 10);
      printf ("After reducing heap the size is %d\n",
	      Cudd_DagSize (res));


      t->theory_debug_dump (tdd);

    }

  res = tdd_exist_abstract (tdd, res, 0);

  
  printf ("The result of existential quantification is: ");
  if (Cudd_ReadOne (cudd) == res)
    printf ("true\n");
  else if (Cudd_ReadLogicZero (cudd) == res)
    printf ("false\n");
  else
    {
      printf ("\n");
      Cudd_PrintMinterm (cudd, res); 
    }
  
  return 0;
}


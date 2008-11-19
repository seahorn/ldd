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




int write_tdd (char* filename, DdManager *cudd, tdd_node *f, char** inames)
{
  FILE* file;
  int res;
  
  file = fopen (filename, "w+");
  res = Cudd_DumpDaVinci(cudd, 1, &f, inames, NULL, file);
  fclose (file);
  return res;
  
}

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
  printf ("Using %d numeric variables\n", size);

  /* 10 = whatever */
/*   Cudd_ReduceHeap (cudd, CUDD_REORDER_SIFT, 10); */
/*   printf ("After reducing heap the size is %d\n", */
/* 	  Cudd_DagSize (bench)); */



/*   fprintf (stdout, "Enabling dynamic reordering\n"); */
/*   /\* default method is CUDD_REORDER_SIFT *\/ */
/*   Cudd_AutodynEnable (cudd, CUDD_REORDER_SAME); */

  printf ("Starting existential quantification\n");
  res = bench;


  
/*   printf ("Writing initial diagram:\n"); */
/*   Cudd_PrintMinterm (cudd, res); */
/*   write_tdd ("initial.dot", cudd, res, NULL); */


  for (i = size - 1 ; i >= 0; i--)
    //for (i = 1; i < size ; i++)
    {
      tdd_node* tmp;
/*       char name[20]; */

      /* Only run quantification when needed */
      if (Cudd_IsConstant (res)) break;

      tmp = tdd_exist_abstract (tdd, res, i);
      Cudd_Ref (tmp);
      Cudd_RecursiveDeref (cudd, res);
      res = tmp;
      printf ("After quantifying x%d the size is %d\n",
	      i, Cudd_DagSize (res));

      printf ("Sanity check:\n");
      tdd_sanity_check (tdd);


/*       printf ("Writting current result\n"); */
/* /\*       Cudd_PrintMinterm (cudd, res); *\/ */
/*       snprintf (name, 20, "qelim-%d.dot", i); */
/*       write_tdd (name, cudd, res, NULL); */
      
      //tdd_manager_debug_dump (tdd);

      /* 10 = whatever */
/*       Cudd_ReduceHeap (cudd, CUDD_REORDER_SIFT, 10); */
/*       printf ("After reducing heap the size is %d\n", */
/* 	      Cudd_DagSize (res)); */


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

  util_print_cpu_stats (stderr);
  
  return 0;
}


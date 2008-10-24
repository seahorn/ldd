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
  bool *vars;

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


  printf ("Starting existential quantification\n");
  res = bench;

  
  vars = (bool*) malloc (sizeof (bool) * size);
  for (i = 0; i < size; i++)
    vars [i] = 1;
  
  res = tdd_exist_abstract_v2 (tdd, res, vars);
  printf ("After quantifying the size is %d\n", Cudd_DagSize (res));
  //tdd_manager_debug_dump (tdd);
 
  //t->theory_debug_dump (t); 

    
  printf ("The result of existential quantification is: ");
  if (tdd_get_true (tdd) == res)  
    printf ("true\n");
  else if (tdd_get_false (tdd) == res)
    printf ("false\n");
  else
    {
      printf ("\n");
      Cudd_PrintMinterm (cudd, res); 
    }

  return 0;
}


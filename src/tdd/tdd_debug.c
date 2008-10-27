#include <stdio.h>

#include "util.h"
#include "tddInt.h"


void tdd_manager_debug_dump (tdd_manager* tdd)
{
  int i;
  
  fprintf (stderr, "tdd_manager @%p\n", tdd);
  fprintf (stderr, "\tcudd @%p, theory @%p\n", tdd->cudd, tdd->theory);
  fprintf (stderr, "\tvarsSize=%d\n", tdd->varsSize);

  for (i = 0; i < tdd->varsSize; i++)
    {
      fprintf (stderr, "\t %d: ", i);
      if (tdd->ddVars [i] == NULL)
	fprintf (stderr, "(nil)");
      else
	tdd->theory->print_lincons (stderr, tdd->ddVars [i]);

      fprintf (stderr, "\n");
    }
}


/**
 * Computes the number of paths in a diagram.  Running time is linear
 * in the number of path, exponential in the size of the diagram.
 */
int tdd_path_size (tdd_manager * tdd, tdd_node * n)
{
  tdd_node * N, *t, *e;
  
  tdd_node *one, *zero;
  
  if (n == NULL) return 0;

  one = tdd_get_true (tdd);
  zero = tdd_not (one);
  
  if (n == one) return 1;
  if (n == zero) return 0;
  
  
  N = Cudd_Regular (n);
  t = cuddT (N);
  e = cuddE (N);

  return tdd_path_size (tdd, t) + tdd_path_size (tdd, e);  
}


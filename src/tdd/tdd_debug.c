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

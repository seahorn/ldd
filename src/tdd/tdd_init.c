#include "util.h"
#include "tddInt.h"


tdd_manager * tdd_init (DdManager *cudd, theory_t * t)
{
  tdd_manager* tdd;
  int i;
  
  tdd = ALLOC(tdd_manager, 1);
  if (tdd == NULL) return 0;
  

  /* set CUDD and theory */
  tdd->cudd = cudd;
  tdd->theory = t;

  /* allocate the map from DD nodes to linear constraints*/
  tdd->varsSize = cudd->maxSize;
  tdd->ddVars = ALLOC(lincons_t,tdd->varsSize);
  if (tdd->ddVars == NULL)
    {
      FREE(tdd);
      return 0;
    }
  for (i = 0; i < tdd->varsSize; i++)
    tdd->ddVars [i] = NULL;
  
  return tdd;
}

void tdd_quit (tdd_manager * tdd)
{
  if (tdd->ddVars != NULL)
    {
      FREE (tdd->ddVars);
      tdd->ddVars = NULL;
    }

  FREE (tdd);
}


tdd_node* to_tdd (tdd_manager *tdd, lincons_t l)
{
  return THEORY->to_tdd(tdd, l);
}


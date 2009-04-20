#include "util.h"
#include "tddInt.h"

static int bin_false (lincons_t, lincons_t);

tdd_manager * 
tdd_init (DdManager *cudd, theory_t * t)
{
  tdd_manager* tdd;
  int i;
  
  tdd = ALLOC(tdd_manager, 1);
  if (tdd == NULL) return 0;
  

  /* set CUDD and theory */
  tdd->cudd = cudd;
  tdd->theory = t;

  tdd->be_bddlike = 0;

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

void 
tdd_quit (tdd_manager * tdd)
{
  if (tdd->ddVars != NULL)
    {
      int i;
      for (i = 0; i < tdd->varsSize; i++)
	if (tdd->ddVars [i] != NULL)
	  {
	    THEORY->destroy_lincons (tdd->ddVars [i]);
	    tdd->ddVars [i] = NULL;
	  }
     
      FREE (tdd->ddVars);
      tdd->ddVars = NULL;
    }
  FREE (tdd);
}


tdd_node* 
to_tdd (tdd_manager *tdd, lincons_t l)
{
  return THEORY->to_tdd(tdd, l);
}


/**
 * Converts a given theory t into a theory in which all implications
 * are syntactic.
 */
theory_t *
tdd_syntactic_implication_theory (theory_t *t)
{
  t->is_stronger_cons = bin_false;
  return t;
}

tdd_manager *
tdd_bddlike_manager (tdd_manager *tdd)
{
  tdd->be_bddlike = 1;
  return tdd;
}


static int 
bin_false (lincons_t l1, lincons_t l2)
{
  return 0;
}

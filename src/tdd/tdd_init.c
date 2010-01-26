#include "util.h"
#include "tddInt.h"

static int bin_false (lincons_t, lincons_t);

LddManager * 
Ldd_Init (DdManager *cudd, theory_t * t)
{
  LddManager* tdd;
  int i;
  
  tdd = ALLOC(LddManager, 1);
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

  /* add a hook to fix MTR tree after variable reordering */
  Cudd_AddHook (CUDD, &Ldd_fix_mtr_tree, CUDD_POST_REORDERING_HOOK);
  
  return tdd;
}

void 
Ldd_Quit (LddManager * tdd)
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


LddNode* 
to_tdd (LddManager *tdd, lincons_t l)
{
  return THEORY->to_tdd(tdd, l);
}


/**
 * Converts a given theory t into a theory in which all implications
 * are syntactic.
 */
theory_t *
Ldd_SyntacticImplicationTheory (theory_t *t)
{
  t->is_stronger_cons = bin_false;
  return t;
}

LddManager *
Ldd_BddlikeManager (LddManager *tdd)
{
  tdd->be_bddlike = 1;
  return tdd;
}


static int 
bin_false (lincons_t l1, lincons_t l2)
{
  return 0;
}

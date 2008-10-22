#include "util.h"
#include "tddInt.h"

static tdd_node * tdd_assoc_node (tdd_manager *, tdd_node *, lincons_t);

tdd_node* tdd_new_var (tdd_manager * tdd, lincons_t l)
{
  tdd_node * n = Cudd_bddNewVar (CUDD);
  
  if (n == NULL)
    return NULL;
  
  
  n = tdd_assoc_node (tdd, n, l);

  return n;
}


tdd_node * tdd_new_var_before (tdd_manager * tdd, tdd_node * v, lincons_t l)
{

  tdd_node * n = Cudd_bddNewVarAtLevel (CUDD, cuddI (CUDD, v->index));
  if (n == NULL) return NULL;

  n = tdd_assoc_node (tdd, n, l);
  return n;
  
}

tdd_node * tdd_assoc_node (tdd_manager * tdd, tdd_node *n, lincons_t l)
{
  int idx;
  int i;
  
  idx = n->index;
  
  if (idx >= tdd->varsSize)
    {
      lincons_t* newDdVars = ALLOC (lincons_t, CUDD->maxSize);
      if (newDdVars == NULL) return NULL;
      
      for (i = 0; i < tdd->varsSize; i++)
	newDdVars [i] = tdd->ddVars [i];
      for (i = tdd->varsSize; i < CUDD->maxSize; i++)
	newDdVars [i] = NULL;
      
      FREE (tdd->ddVars);
      tdd->varsSize = CUDD->maxSize;
      tdd->ddVars = newDdVars;
    }
  
  tdd->ddVars [idx] = THEORY->dup_lincons (l);

  return n;
}


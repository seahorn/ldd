#include "util.h"
#include "tddInt.h"

/** BDD Style existential quantification */
tdd_node * 
tdd_bdd_exist_abstract (tdd_manager * tdd,
			tdd_node * f,
			tdd_node * cube)
{
  DdNode *res;
  
  do
    {
      CUDD->reordered = 0;
      res = tdd_bdd_exist_abstract_recur (tdd, f, cube);
    } while (CUDD->reordered == 1);

  return res;
}


/**
 * Over-approximates existential quantification of all variables in
 * Boolean array vars.
 */
tdd_node * 
tdd_over_abstract (tdd_manager *tdd, 
		   tdd_node * f, 
		   bool * vars)
{

  tdd_node *res;
  tdd_nodeset* varset;

  
  varset = tdd_terms_with_vars (tdd, vars);
  
  if (varset == NULL) return NULL;
  cuddRef (varset);

  res = tdd_bdd_exist_abstract (tdd, f, varset);

  if (res != NULL)
    cuddRef (res);
  
  Cudd_IterDerefBdd (CUDD, varset);

  if (res != NULL)
    cuddDeref (res);

  return res;
}


/**
 * Constructs a cube of all of the terms that contains variables in
 * the Boolean array vars.
 */
tdd_nodeset *
tdd_terms_with_vars (tdd_manager *tdd,
		     bool * vars)
{
  tdd_nodeset * res;
  
  int i;

  res = (tdd_nodeset*) tdd_get_true (tdd); //tdd_empty_nodeset (tdd);
  cuddRef (res);
  
  for (i = tdd->varsSize - 1; i >= 0; i--)
    {
      if (tdd->ddVars [i] == NULL) continue;
      
      if (THEORY->term_has_vars (THEORY->get_term (tdd->ddVars [i]), vars))
	{
	  tdd_nodeset *tmp;

	  tmp = tdd_nodeset_add (tdd, res, CUDD->vars [i]);
	  if (tmp != NULL) cuddRef (tmp);
	  Cudd_IterDerefBdd (CUDD, res);
	  if (tmp == NULL) return NULL;
	  res = tmp;
	}
    }

  cuddDeref (res);
  return res;
    
}



/* taken from cuddBddAbs.c/cuddBddExistAbstractRecur */
tdd_node *
tdd_bdd_exist_abstract_recur (tdd_manager *tdd,
			      tdd_node *f,
			      tdd_nodeset *varset)
{
  tdd_node *F, *T, *E, *res, *res1, *res2, *one;
  DdManager *manager;
  

  manager = CUDD;
  statLine (manager);
  one = DD_ONE (manager);
  F = Cudd_Regular (f);
  
  if (varset == one || F == one) return (f);
  
    /* Abstract a variable that does not appear in f. */
    while (manager->perm[F->index] > manager->perm[varset->index]) {
      varset = Cudd_Regular (cuddE(varset));
      if (varset == one) return(f);
    }

    /* Check the cache. */
    if (F->ref != 1 && 
	(res = cuddCacheLookup2(manager, 
				(DD_CTFP)tdd_bdd_exist_abstract, 
				f, varset)) != NULL) {
	return(res);
    }

    /* Compute the cofactors of f. */
    T = cuddT(F); E = cuddE(F);
    if (f != F) {
	T = Cudd_Not(T); E = Cudd_Not(E);
    }

    /* If the two indices are the same, so are their levels. */
    if (F->index == varset->index) {
	if (T == one || E == one || T == Cudd_Not(E)) {
	    return(one);
	}
	res1 = 
	  tdd_bdd_exist_abstract_recur(tdd, T, Cudd_Regular(cuddE(varset)));
	if (res1 == NULL) return(NULL);
	if (res1 == one) {
	    if (F->ref != 1)
	      cuddCacheInsert2(manager, 
			       (DD_CTFP)tdd_bdd_exist_abstract, f, varset, one);
	    return(one);
	}
        cuddRef(res1);
	res2 = tdd_bdd_exist_abstract_recur(tdd, E, 
					    Cudd_Regular (cuddE(varset)));
	if (res2 == NULL) {
	    Cudd_IterDerefBdd(manager,res1);
	    return(NULL);
	}
        cuddRef(res2);
	res = tdd_and_recur(tdd, Cudd_Not(res1), Cudd_Not(res2));
	if (res == NULL) {
	    Cudd_IterDerefBdd(manager, res1);
	    Cudd_IterDerefBdd(manager, res2);
	    return(NULL);
	}
	res = Cudd_Not(res);
	cuddRef(res);
	Cudd_IterDerefBdd(manager, res1);
	Cudd_IterDerefBdd(manager, res2);
	if (F->ref != 1)
	  cuddCacheInsert2(manager, 
			   (DD_CTFP)tdd_bdd_exist_abstract, f, varset, res);
	cuddDeref(res);
        return(res);
    } else { /* if (cuddI(manager,F->index) < cuddI(manager,cube->index)) */
	res1 = tdd_bdd_exist_abstract_recur(tdd, T, varset);
	if (res1 == NULL) return(NULL);
        cuddRef(res1);
	res2 = tdd_bdd_exist_abstract_recur(tdd, E, varset);
	if (res2 == NULL) {
	    Cudd_IterDerefBdd(manager, res1);
	    return(NULL);
	}
        cuddRef(res2);
	/* ITE takes care of possible complementation of res1 and of the
        ** case in which res1 == res2. */
	res = tdd_ite_recur(tdd, manager->vars[F->index], res1, res2);
	if (res == NULL) {
	    Cudd_IterDerefBdd(manager, res1);
	    Cudd_IterDerefBdd(manager, res2);
	    return(NULL);
	}
	cuddRef (res);
	Cudd_IterDerefBdd (manager, res1);
	Cudd_IterDerefBdd (manager, res2);
	if (F->ref != 1)
	  cuddCacheInsert2(manager, 
			   (DD_CTFP)tdd_bdd_exist_abstract, f, varset, res);
	cuddDeref (res);
        return(res);
    }	    
  
}

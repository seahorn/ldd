#include "util.h"
#include "tddInt.h"

/** \brief BDD-style existential quantification */
LddNode * 
Ldd_BddExistAbstract (LddManager * ldd,
			LddNode * f,
			LddNode * cube)
{
  DdNode *res;
  
  do
    {
      CUDD->reordered = 0;
      res = lddBddExistAbstractRecur (ldd, f, cube);
    } while (CUDD->reordered == 1);

  return res;
}


/**
 * \brief Over-approximates existential quantification of all
  variables in Boolean array vars by eliminating all terms with those
  variables
 */
LddNode * 
Ldd_OverAbstract (LddManager *ldd, 
		   LddNode * f, 
		   bool * vars)
{

  LddNode *res;
  LddNodeset* varset;

  
  varset = Ldd_TermsWithVars (ldd, vars);
  
  if (varset == NULL) return NULL;
  cuddRef (varset);

  res = Ldd_BddExistAbstract (ldd, f, varset);

  if (res != NULL)
    cuddRef (res);
  
  Cudd_IterDerefBdd (CUDD, varset);

  if (res != NULL)
    cuddDeref (res);

  return res;
}


/**
 * \brief Constructs a nodeset of all of the terms that contain
  variables in the Boolean array vars.
 */
LddNodeset *
Ldd_TermsWithVars (LddManager *ldd,
		   bool * vars)
{
  LddNodeset * res;
  
  int i;

  res = (LddNodeset*) Ldd_GetTrue (ldd); 
  cuddRef (res);
  
  for (i = ldd->varsSize - 1; i >= 0; i--)
    {
      if (ldd->ddVars [i] == NULL) continue;
      
      if (THEORY->term_has_vars (THEORY->get_term (ldd->ddVars [i]), vars))
	{
	  LddNodeset *tmp;
	  
	  tmp = Ldd_NodesetUnion (ldd, Ldd_NodeToNodeset (CUDD->vars [i]), res);
	  if (tmp != NULL) cuddRef (tmp);
	  Cudd_IterDerefBdd (CUDD, res);
	  if (tmp == NULL) return NULL;
	  res = tmp;
	}
    }

  cuddDeref (res);
  return res;
    
}



/**
 * \brief Recursive step of Ldd_BddExistAbstract
 
 based on cuddBddAbs.c/cuddBddExistAbstractRecur
 */
LddNode *
lddBddExistAbstractRecur (LddManager *ldd,
			      LddNode *f,
			      LddNodeset *varset)
{
  LddNode *F, *T, *E, *res, *res1, *res2, *one;
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
				(DD_CTFP)Ldd_BddExistAbstract, 
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
	  lddBddExistAbstractRecur(ldd, T, Cudd_Regular(cuddE(varset)));
	if (res1 == NULL) return(NULL);
	if (res1 == one) {
	    if (F->ref != 1)
	      cuddCacheInsert2(manager, 
			       (DD_CTFP)Ldd_BddExistAbstract, f, varset, one);
	    return(one);
	}
        cuddRef(res1);
	res2 = lddBddExistAbstractRecur(ldd, E, 
					    Cudd_Regular (cuddE(varset)));
	if (res2 == NULL) {
	    Cudd_IterDerefBdd(manager,res1);
	    return(NULL);
	}
        cuddRef(res2);
	res = lddAndRecur(ldd, Cudd_Not(res1), Cudd_Not(res2));
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
			   (DD_CTFP)Ldd_BddExistAbstract, f, varset, res);
	cuddDeref(res);
        return(res);
    } else { /* if (cuddI(manager,F->index) < cuddI(manager,cube->index)) */
	res1 = lddBddExistAbstractRecur(ldd, T, varset);
	if (res1 == NULL) return(NULL);
        cuddRef(res1);
	res2 = lddBddExistAbstractRecur(ldd, E, varset);
	if (res2 == NULL) {
	    Cudd_IterDerefBdd(manager, res1);
	    return(NULL);
	}
        cuddRef(res2);
	/* ITE takes care of possible complementation of res1 and of the
        ** case in which res1 == res2. */
	res = lddIteRecur(ldd, manager->vars[F->index], res1, res2);
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
			   (DD_CTFP)Ldd_BddExistAbstract, f, varset, res);
	cuddDeref (res);
        return(res);
    }	    
  
}

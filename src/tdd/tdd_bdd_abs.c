#include "util.h"
#include "tddInt.h"

/** BDD Style existential quantification */
LddNode * 
Ldd_BddExistAbstract (LddManager * tdd,
			LddNode * f,
			LddNode * cube)
{
  DdNode *res;
  
  do
    {
      CUDD->reordered = 0;
      res = Ldd_bdd_exist_abstract_recur (tdd, f, cube);
    } while (CUDD->reordered == 1);

  return res;
}


/**
 * Over-approximates existential quantification of all variables in
 * Boolean array vars.
 */
LddNode * 
Ldd_OverAbstract (LddManager *tdd, 
		   LddNode * f, 
		   bool * vars)
{

  LddNode *res;
  LddNodeset* varset;

  
  varset = Ldd_TermsWithVars (tdd, vars);
  
  if (varset == NULL) return NULL;
  cuddRef (varset);

  res = Ldd_BddExistAbstract (tdd, f, varset);

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
LddNodeset *
Ldd_TermsWithVars (LddManager *tdd,
		     bool * vars)
{
  LddNodeset * res;
  
  int i;

  res = (LddNodeset*) Ldd_GetTrue (tdd); //Ldd_empty_nodeset (tdd);
  cuddRef (res);
  
  for (i = tdd->varsSize - 1; i >= 0; i--)
    {
      if (tdd->ddVars [i] == NULL) continue;
      
      if (THEORY->term_has_vars (THEORY->get_term (tdd->ddVars [i]), vars))
	{
	  LddNodeset *tmp;
	  
	  //assert (is_valid_nodeset (tdd, res) && "Before ADD");
	  //tmp = Ldd_NodesetAdd (tdd, res, CUDD->vars [i]);
	  tmp = Ldd_NodesetUnion (tdd, Ldd_NodeToNodeset (CUDD->vars [i]), res);
	  //assert (is_valid_nodeset (tdd, tmp) && "After ADD");
	  if (tmp != NULL) cuddRef (tmp);
	  Cudd_IterDerefBdd (CUDD, res);
	  if (tmp == NULL) return NULL;
	  res = tmp;
	  //assert (is_valid_nodeset (tdd, res) && "END OF LOOP");
	}
    }

  cuddDeref (res);
  return res;
    
}



/* taken from cuddBddAbs.c/cuddBddExistAbstractRecur */
LddNode *
Ldd_bdd_exist_abstract_recur (LddManager *tdd,
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
	  Ldd_bdd_exist_abstract_recur(tdd, T, Cudd_Regular(cuddE(varset)));
	if (res1 == NULL) return(NULL);
	if (res1 == one) {
	    if (F->ref != 1)
	      cuddCacheInsert2(manager, 
			       (DD_CTFP)Ldd_BddExistAbstract, f, varset, one);
	    return(one);
	}
        cuddRef(res1);
	res2 = Ldd_bdd_exist_abstract_recur(tdd, E, 
					    Cudd_Regular (cuddE(varset)));
	if (res2 == NULL) {
	    Cudd_IterDerefBdd(manager,res1);
	    return(NULL);
	}
        cuddRef(res2);
	res = Ldd_and_recur(tdd, Cudd_Not(res1), Cudd_Not(res2));
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
	res1 = Ldd_bdd_exist_abstract_recur(tdd, T, varset);
	if (res1 == NULL) return(NULL);
        cuddRef(res1);
	res2 = Ldd_bdd_exist_abstract_recur(tdd, E, varset);
	if (res2 == NULL) {
	    Cudd_IterDerefBdd(manager, res1);
	    return(NULL);
	}
        cuddRef(res2);
	/* ITE takes care of possible complementation of res1 and of the
        ** case in which res1 == res2. */
	res = Ldd_ite_recur(tdd, manager->vars[F->index], res1, res2);
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

#include "util.h"
#include "lddInt.h"

/**
   Computes post of "x := x + y" on an input Boxes LDD.

   ldd -- the manager
   f   -- input Boxes LDD
   x   -- term being assigned
   y   -- term being added
 */
LddNode *
Ldd_BoxesXpy (LddManager *ldd, LddNode *f, linterm_t x, linterm_t y)
{
  LddNode *res;
  DdLocalCache *cache;
  
  do
    {
      CUDD->reordered = 0;
      cache = cuddLocalCacheInit (CUDD, 1, 2, CUDD->maxCacheHard);
      if (cache == NULL) return NULL;
      
      int xlevel = THEORY->term_level (x);
      int ylelel = THEORY->term_level (y);
      
      assert (xlevel != ylevel);
      if (x < y) 
	res = lddBoxesXpy1 (ldd, f, x, y, NULL, cache);
      else 
	res = lddBoxesXpy2 (ldd, f, x, y, NULL, cache);
      if (res != NULL)
	cuddRef (res);
      cuddLocalCacheQuit (cache);
    }
  while (CUDD->reordered == 1);

  if (res != NULL) cuddDeref (res);
  return (res);
}


/**
   Recursive step of Ldd_BoxesXpy when level(x) < level(y)
 */
LddNode* 
lddBoxesXpy1 (LddManager *ldd, LddNode *f, linterm_t x, 
	      linterm_t y, constant_t xlbound, DdLocalCache *cache)
{
  DdNode *F, *t, *e, *r, *tmp;
  lincons_t fCons;
  linterm_t fTerm;
  constant_t fCst;
  unsigned int topf;

  unsigned int xlevel;
  
  F = Cudd_Regular (f);

  /* f is a constant */
  if (F == DD_ONE (CUDD)) return f;

  if (F->ref != 1 && (r = cuddLocalCacheLookup (cache, &f)) != NULL)
    return r;
  
  xlevel = THEORY->term_level (ldd, x);
  fCons = ldd->ddVars [F->index];
  fTerm = THEORY->get_term (fCons);
  topf = CUDD->perm [F->index];
  
  if (topf > xlevel)
    {
      if (xlbound == NULL)  return f;
      else return lddTermReplace (ldd, f, x, y, cst1, xlbound, NULL);
    }
  
  t = Cudd_NotCond (cuddT(F), f != F);
  cuddRef (t);

  e = Cudd_NotCond (cuddE(F), f != F);
  cuddRef (e);

  if (!THEORY->term_equals (x, fTerm))
    { 
      /* recurse on 'then' branch */
      tmp = lddBoxesXpy1 (ldd, t, x, y, xlbound, cache);
      if (tmp == NULL) 
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  Cudd_IterDerefBdd (CUDD, e);
	  return NULL;
	}
      cuddRef (tmp);
      Cudd_IterDerefBdd (CUDD, t);
      t = tmp;
      
      /* recurse on 'else' branch */
      tmp = lddBoxesXpy1 (ldd, e, x, y, xlbound, cache);
      if (tmp == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  Cudd_IterDerefBdd (CUDD, e);
	  return NULL;
	}
      cuddRef (tmp);
      Cudd_IterDerefBdd (CUDD, e);
      e = tmp;
      
      /* build ITE for the result */
      DdNode *root = Cudd_bddIthVar (CUDD, F->index);
      cuddRef (root);
      /* XXX can use Ldd_Unique_Inter instead */
      r = lddIteRecur (ldd, root, t, e);
      if (r != NULL) 
	{
	  cuddRef (r);
	  if (xlbound == NULL && F->ref != 1)
	    cuddLocalCacheLookup (cache, &f, r);
	}
      Cudd_IterDerefBdd (CUDD, root);
      Cudd_IterDerefBdd (CUDD, t);
      Cudd_IterDerefBdd (CUDD, e);
      if (r != NULL) cuddDeref (r);
      return r;
    }

  /* ELSE (THEORY->term_equals (x, fTerm) */

  tmp = lddTermReplace (ldd, t, x, y, cst1, xlbound, xubound);
  if (tmp == NULL)
    {
      Cudd_IterDerefBdd (CUDD, t);
      Cudd_IterDerefBdd (CUDD, e);
      return NULL;
    }
  cuddRef (tmp);
  Cudd_IterDerefBdd (CUDD, t);
  t = tmp;


  tmp = lddBoxesXpy1 (ldd, e, x, y, new_xlbound);
  if (tmp == NULL)
    {
      Cudd_IterDerefBdd (CUDD, t);
      Cudd_IterDerefBdd (CUDD, e);
      return NULL;
    }
  cuddRef (tmp);
  Cudd_IterDerefBdd (CUDD, e);
  e = tmp;

  r = lddAndRecur (ldd, Cudd_Not (t), Cudd_Not (e));
  if (r == NULL)
    {
      Cudd_IterDerefBdd (CUDD, t);
      Cudd_IterDerefBdd (CUDD, e);
      return NULL;
    }
  cuddRef (r);
  r = Cudd_Not (r);
  Cudd_IterDerefBdd (CUDD, t);
  Cudd_IterDerefBdd (CUDD, e);
      
  if (xlbound == NULL && F->ref != 1)
    cuddLocalCacheInsert (cache, &f, r);
  cuddDeref (r);
  return r;
}

/**
   Recursive step of Ldd_BoxesXpy when  level(y) < level (x)
 */
LddNode*
lddBoxesXpy2 (LddManager *ldd, LddNode *f, linterm_t x, 
	      linterm_t y, constant_t ylbound, DdLocalCache *cache)
{
  return NULL;
}

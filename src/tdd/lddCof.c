#include "util.h"
#include "tddInt.h"

/**
   \brief Computes a cofactor of f with respect to g
   
   \pre g is an LDD cube.

   \return a pointer to the cofactor if successful; NULL otherwise.

   Based on Cudd_Cofactor
 */
LddNode *
Ldd_Cofactor (LddManager *ldd,
	      DdNode *f,
	      DdNode *g)
{
  DdNode *res, *zero;
  
  zero = Cudd_Not (DD_ONE(CUDD));
  if (g == zero)
  {
    (void) fprintf(CUDD->err,"Ldd_Cofactor: Invalid restriction 1\n");
    CUDD->errorCode = CUDD_INVALID_ARG;
    return(NULL);
  }    
  
  do
    {
      CUDD->reordered = 0;
      res = lddCofactorRecur (ldd, f, g);
    }
  while (CUDD->reordered == 1);
  return res;
}

LddNode *
lddCofactorRecur (LddManager *ldd,
		  LddNode *f,
		  LddNode *g)
{
  DdManager * manager;
  DdNode *F, *fv, *fnv, *G, *gv, *gnv;
  DdNode *one, *zero, *r, *t, *e;
  unsigned int topf, topg, index;

  lincons_t vCons;
  int comple;
  

  manager = CUDD;
  statLine(manager);

  F = Cudd_Regular (f);
  if (cuddIsConstant (F)) return f;

  one = DD_ONE(manager);
  zero = Cudd_Not (one);

  if (g == one) return f;

  comple = f != F;

  /* At this point f and g are not constant. */  
  r = cuddCacheLookup2 (CUDD, (DD_CTFP)Ldd_Cofactor, F, g);
  if (r != NULL)
    return Cudd_NotCond (r, comple);

  
  /* Get the levels */
  /* Here we can skip the use of cuddI, because the operands are known
  ** to be non-constant.
  */
  topf = manager->perm[F->index];
  G = Cudd_Regular(g);
  topg = manager->perm[G->index];

  /* Compute cofactors of F. */
  if (topf <= topg) {
    index = F->index;
    fv = cuddT(F);
    fnv = cuddE(F);
  } else {
    index = G->index;
    fv = fnv = f;
  }
  
  if (topg <= topf) {
    gv = cuddT(G);
    gnv = cuddE(G);
    if (Cudd_IsComplement(g)) {
      gv = Cudd_Not(gv);
      gnv = Cudd_Not(gnv);
    }
  } else {
    gv = gnv = g;
  }


  /** 
   * Get the constraint of the root node 
   */
  vCons = lddC (ldd, index);

  /** 
   * Compute LDD cofactors w.r.t. the top term.  
   * 
   * We check whether f and g have the same constraint using the
   * following facts: 
   *   vCons is the constraint of the root diagram
   *   gv == g iff g is not the root diagram
   *   fv == f iff f is not the root diagram
   */
  if (gv == g)
    {
      lincons_t gCons = lddC (ldd, G->index);
      
      if (THEORY->is_stronger_cons (vCons, gCons))
	{
	  gv = cuddT (G);
	  if (Cudd_IsComplement (g))
	    gv = Cudd_Not (gv);
	}
    }
  else if (fv == f)
    {
      lincons_t fCons = lddC (ldd, F->index);
      
      if (THEORY->is_stronger_cons (vCons, fCons))
	fv = cuddT (F);
    }

  
  if (topf >= topg)
    {
      if (gnv == zero)
	r = lddCofactorRecur (ldd, fv, gv);
      else if (gv == zero)
	r = lddCofactorRecur (ldd, fnv, gnv);
      else
	{
	  (void) fprintf(CUDD->err,
			 "Cudd_Cofactor: Invalid restriction 2\n");
	  CUDD->errorCode = CUDD_INVALID_ARG;
	  return(NULL);	  
	}
    }
  else if (topf < topg && gv == zero)
    {
      /* gv == zero IMPLIES gv != g */
      /* topf and topg share a term and lddC(f) implies lddC(g) */
      r = lddCofactorRecur (ldd, fnv, g);
    }
  
  else /* if (topf < topg) */
    {
      t = lddCofactorRecur (ldd, fv, g);
      if (t == NULL) return NULL;
      cuddRef (t);
      e = lddCofactorRecur (ldd, fnv, g);
      if (e == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  return NULL;
	}
      cuddRef (e);
      
      if (t == e)
	r = t;
      else if (Cudd_IsComplement (t))
	{
	  r = lddUniqueInter (ldd, (int) F->index, Cudd_Not (t), Cudd_Not (e));
	  r = Cudd_NotCond (r, r != NULL);
	}
      else
	r = lddUniqueInter (ldd, (int) F->index, t, e);
      
      if (r != NULL) cuddRef (r);
      Cudd_IterDerefBdd (CUDD, t);
      Cudd_IterDerefBdd (CUDD, e);
      if (r == NULL) return NULL;
      cuddDeref (r);
    }

  cuddCacheInsert2 (CUDD,  (DD_CTFP)Ldd_Cofactor, F, g, r);
  return Cudd_NotCond (r, comple);
  
}


	      

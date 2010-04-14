/**
   Quantifier elimination using Fourier-Motzkin
 */
#include "util.h"
#include "lddInt.h"

/**
   \brief Existential quantification using Fourier-Motzkin.
 */
LddNode *
Ldd_ExistsAbstractFM (LddManager * ldd,
		      LddNode * f,
		      int var)
{
  LddNode *res;
  DdLocalCache *cache;

  

  do 
    {
      CUDD->reordered = 0;

      cache = cuddLocalCacheInit (CUDD, 1, 2, CUDD->maxCacheHard);
      if (cache == NULL) return NULL;
      
      res = lddExistsAbstractFMRecur (ldd, f, var, cache);
      if (res != NULL)
	cuddRef (res);
      cuddLocalCacheQuit (cache);
    } while (CUDD->reordered == 1);
  
  if (res != NULL) cuddDeref (res);

  return res;
}


/**
   \brief Less aggressive version of Ldd_ExistsAbstractFM(). Useful
   for benchmarks/comparison.

   \sa Ldd_ExistsAbstractFM()
 */
LddNode *
Ldd_ExistsAbstractSFM (LddManager * ldd,
		       LddNode * f,
		       int var)
{
  LddNode *res;
  DdLocalCache *cache;
  
  do 
    {
      CUDD->reordered = 0;
      cache = cuddLocalCacheInit (CUDD, 1, 2, CUDD->maxCacheHard);
      if (cache == NULL) return NULL;
      
      res = lddExistsAbstractSFMRecur (ldd, f, var, cache);
      if (res != NULL)
	cuddRef (res);
      cuddLocalCacheQuit (cache);
    } while (CUDD->reordered == 1);
  
  if (res != NULL) cuddDeref (res);
  return res;
}

/**
   \brief Resolve an LDD with a given constraint on a given variable.
   

   \param ldd LDD manager
   \param f   the given LDD
   \param t   the (positive) term of the constraint being resolved
   \param negCons   constraint being resolved with of the form -t < k or NULL
   \param posCons   constraint being resolved with of the form t < k or NULL
   \param var   variable being resolved on

   \sa Ldd_ExistsAbstractFM(), Ldd_ExistsAbstractSFM(), Ldd_Resolve()
 */
LddNode * 
Ldd_Resolve (LddManager * ldd, 
	     LddNode * f, 
	     linterm_t t, 
	     lincons_t negCons, 
	     lincons_t posCons, 
	     int var)
{
  LddNode *res;
  DdHashTable *table;

  do
    {
      CUDD->reordered = 0;
      table = cuddHashTableInit (CUDD, 1, 2);
      if (table == NULL) return NULL;
      
      res = lddResolveRecur (ldd, f, t, negCons, posCons, var, table);
      if (res != NULL)
	cuddRef (res);
      cuddHashTableQuit (table);
    } 
  while (CUDD->reordered == 1);
  
  if (res != NULL) cuddDeref (res);
  return res;

}


/**
   \brief Resolve an LDD with a given constraint on a given variable
   while eliminating all constraints with a given term. Represents the
   main step in the Fourier-Motzkin quantifier elimination procedure.

   \param ldd LDD manager
   \param f   the given LDD
   \param t   the (positive) term being eliminated
   \param cons   constraint being resolved with 
   \param var   variable being resolved on

   \pre  t is positive. t is the term of c. x is a variable in c.

   \sa Ldd_ExistsAbstractFM(), Ldd_ExistsAbstractSFM(), Ldd_Resolve()
 */
LddNode * 
Ldd_ResolveElim (LddManager * ldd, LddNode * f, 
		 linterm_t t, lincons_t cons, int var)
{
  LddNode *res;
  do
    {
      CUDD->reordered = 0;
      res = lddResolveElimInter (ldd, f, t, cons, var);
    } 
  while (CUDD->reordered == 1);
  
  return res;

}



/**
   \brief DVO unaware version of Ldd_ResolveElim().

 * \sa Ldd_ResolveElim()
 */
LddNode * 
lddResolveElimInter (LddManager * ldd, 
		     LddNode * f, 
		     linterm_t t, 
		     lincons_t cons, 
		     int var)
{
  LddNode *res;
  bool isNeg;

  isNeg = THEORY->is_negative_cons (cons);
  
  /* assert: t is a positive term 
   * cons is either t <= c, t < c or -t <= c, -t < c
   */
  
  res = lddResolveElimRecur (ldd, f, 
				t, 
				isNeg ? cons : NULL, 
				isNeg ? NULL : cons, 
				var);
  return res;
}


/**
   \brief Recursive part of Ldd_Resolve().
   
 * Recursive part of Ldd_resolve. Resolves negCons and posCons with
 * LDD f.  t is the term of posCons and -t is the term of negCons. var
 * is the resolution variable. table is the hashtable to keep computed
 * results.
 
 \sa lddResolveElimRecur()
 */
LddNode *
lddResolveRecur (LddManager * ldd,
		   LddNode * f,
		   linterm_t t,
		   lincons_t negCons,
		   lincons_t posCons,
		   int var,
		   DdHashTable *table)
{

  DdNode *one, *zero;
  DdManager * manager;
  
  DdNode *res;
  DdNode *F, *T, *E;

  DdNode *root;
  

  DdNode *fv, *fnv;
  unsigned int v;


  
  /** new constraint for the THEN branch. NULL if the constraint is
      empty. */
  lincons_t tCons;
  
  
  /** new constraint for the ELSE branch. NULL is the constraint is empty.*/
  lincons_t eCons;
  bool fResolve;  

  /* constraint at the root of f */
  lincons_t vCons;
  linterm_t vTerm;


  manager = CUDD;
  one = DD_ONE (manager);
  zero = Cudd_Not (one);

  F = Cudd_Regular (f);
  
  if (cuddIsConstant (F)) return (f);
  
  if (negCons == NULL && posCons == NULL) return (f);

  /* check cache */
  if (F->ref != 1 && ((res = cuddHashTableLookup1(table,f)) != NULL))
    return res;


  /* get index and constraint of the root node */
  v = F->index;
  vCons = lddC (ldd, v);
  vTerm = THEORY->get_term (vCons);
  
  /* get THEN and ELSE branches */
  fv = cuddT (F);
  fnv = cuddE (F);  

  /* compute cofactors */
  fv = Cudd_NotCond (fv, f != F);
  fnv = Cudd_NotCond (fnv, f != F);

  /** recursive call */
  T = lddResolveRecur (ldd, fv, t, negCons, posCons, var, table);

  if (T == NULL) return NULL;
  cuddRef (T);

  /* recursive call */
  E = lddResolveRecur (ldd, fnv, t, negCons, posCons, var, table);

  if (E == NULL) 
    {
      Cudd_IterDerefBdd (manager, T);
      return NULL;
    }
  cuddRef (E);


  /* Compute additional constraints on THEN and ELSE branches by
   * resolving the root constraint vCons with posCons and negCons*/

  tCons = NULL;
  eCons = NULL;  
  fResolve = THEORY->terms_have_resolvent (vTerm, t, var);

  if (fResolve > 0)
    {
      if (posCons != NULL)
	tCons = THEORY->resolve_cons (vCons, posCons, var);

      if (negCons != NULL)
	{
	  lincons_t nvCons = THEORY->negate_cons (vCons);
	  eCons = THEORY->resolve_cons (nvCons, negCons, var);
	  THEORY->destroy_lincons (nvCons);
	}
    }
  else if (fResolve < 0)
    {
      if (negCons != NULL)
	tCons = THEORY->resolve_cons (vCons, negCons, var);

      if (posCons != NULL)
	{
	  lincons_t nvCons = THEORY->negate_cons (vCons);
	  eCons = THEORY->resolve_cons (nvCons, posCons, var);
	  THEORY->destroy_lincons (nvCons);
	}
    }  
  

  /** rebuild T and E using new constraints */
  if (tCons != NULL)
    {
      DdNode *c;
      DdNode *tmp;

      c = THEORY->to_ldd (ldd, tCons);
      THEORY->destroy_lincons (tCons);
      tCons = NULL;

      if (c == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  if (eCons != NULL)
	    THEORY->destroy_lincons (eCons);
	  return NULL;
	}
      cuddRef (c);

      
      
      tmp = lddAndRecur (ldd, c, T);
  
      if (tmp == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  Cudd_IterDerefBdd (manager, c);
	  if (eCons != NULL)
	    THEORY->destroy_lincons (eCons);	  
	  return NULL;
	}
      cuddRef (tmp);

      Cudd_IterDerefBdd (manager, T);
      Cudd_IterDerefBdd (manager, c);
      T = tmp;
    }
  
  if (eCons != NULL)
    {
      DdNode *c;
      DdNode *tmp;

      c = THEORY->to_ldd (ldd, eCons);
      THEORY->destroy_lincons (eCons);
      eCons = NULL;
      
      if (c == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  return NULL;
	}
      cuddRef (c);

            
      tmp = lddAndRecur (ldd, c, E);

      if (tmp == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  Cudd_IterDerefBdd (manager, c);
	  return NULL;
	}
      cuddRef (tmp);
      Cudd_IterDerefBdd (manager, E);
      Cudd_IterDerefBdd (manager, c);
      E = tmp;
    }
  
  

  /* build the final diagram */
  root = Cudd_bddIthVar (manager, v);
  if (root == NULL)
    {
      Cudd_IterDerefBdd (manager, T);
      Cudd_IterDerefBdd (manager, E);
      return NULL;
    }
  cuddRef (root);

  res = lddIteRecur (ldd, root, T, E);
  if (res == NULL)
    {
      Cudd_IterDerefBdd (manager, T);
      Cudd_IterDerefBdd (manager, E);
      Cudd_IterDerefBdd (manager, root);
      return NULL;
    }
  cuddRef (res);



  Cudd_IterDerefBdd (manager, root);
  root = NULL;

  Cudd_IterDerefBdd (manager, T);
  T = NULL;
  Cudd_IterDerefBdd (manager, E);
  E = NULL;
      
      
  /* save result in a hashtable, but only if it will be needed */
  if (F->ref != 1)
    {
      ptrint fanout = (ptrint) F->ref;
      cuddSatDec (fanout);
      if (!cuddHashTableInsert1 (table, f, res, fanout))
	{
	  Cudd_IterDerefBdd (manager, res);
	  return NULL;
	}
    }

  /* return the result */
  cuddDeref (res);
  return res;
}



/**
 * \brief Recursive part of lddResolveElimRecur().
 *
   \param ldd LDD manager
   \param f   the given LDD
   \param t   the (positive) term being eliminated
   \param negCons   constraint being resolved with of the form -t <= k or NULL
   \param posCons   constraint being resolved with of the form t <= k or NULL
   \param var   variable being resolved on

 */
LddNode *
lddResolveElimRecur (LddManager * ldd,
		     LddNode * f,
		     linterm_t t,
		     lincons_t negCons,
		     lincons_t posCons,
		     int var)
{

  DdManager * manager;
  
  DdNode *res;
  DdNode *F, *T, *E;

  DdNode *fv, *fnv;
  unsigned int v;

  /* constraint at the root of f */
  lincons_t vCons;
  linterm_t vTerm;

  manager = CUDD;
  F = Cudd_Regular (f);
  
  if (F == DD_ONE(CUDD)) return (f);
  
  if (negCons == NULL && posCons == NULL) return (f);

  /* terminal case. upper bound cannot be overwritten. */
  if (posCons != NULL)
    {
      DdHashTable *table;
      LddNode * r;
      
      table = cuddHashTableInit (CUDD, 1, 2);
      if (table == NULL) return NULL;

      r = lddResolveRecur (ldd, f, t, negCons, posCons, var, table);

      if (r != NULL) cuddRef (r);
      cuddHashTableQuit (table);
      if (r != NULL) cuddDeref (r);

      return r;
    }
  


  /* assert: posCons == NULL && negCons != NULL */


  /* get index and constraint of the root node */
  v = F->index;
  vCons = ldd->ddVars [v];
  vTerm = THEORY->get_term (vCons);


  /* terminal case. bounds cannot change. */
  if (!THEORY->term_equals (vTerm, t))
    {
      DdHashTable* table;
      LddNode * r;

      table = cuddHashTableInit (CUDD, 1, 2);
      if (table == NULL) return NULL;      

      r = lddResolveRecur (ldd, f, t, negCons, posCons, var, table);

      if (r != NULL) cuddRef (r);
      cuddHashTableQuit (table);
      if (r != NULL) cuddDeref (r);

      return r;
    }
  
  

  /* assert: vTerm == t */
  
  /* for the THEN branch let posCons = vCons.
     for the ELSE branch let negCons = negate (vCons), posCons = NULL
  */

  /* get THEN and ELSE branches */
  fv = cuddT (F);
  fnv = cuddE (F);  

  /* compute cofactors */
  fv = Cudd_NotCond (fv, f != F);
  fnv = Cudd_NotCond (fnv, f != F);



  /** recursive call */
  T = lddResolveElimRecur (ldd, fv, t, negCons, vCons, var);
  if (T == NULL) return NULL;
  cuddRef (T);
  
  {
    lincons_t nvCons = THEORY->negate_cons (vCons);
    E = lddResolveElimRecur (ldd, fnv, t, nvCons, (lincons_t)NULL, var);  
    THEORY->destroy_lincons (nvCons);
  }
  

  if (E == NULL) 
    {
      Cudd_IterDerefBdd (manager, T);
      return NULL;
    }
  cuddRef (E);

  res = lddAndRecur (ldd, Cudd_Not(T), Cudd_Not(E));
  if (res == NULL)
    {
      Cudd_IterDerefBdd (manager, T);
      Cudd_IterDerefBdd (manager, E);
      return NULL;
    }
  res = Cudd_Not (res);
  cuddRef (res);
  Cudd_IterDerefBdd (manager, T);
  T = NULL;
  Cudd_IterDerefBdd (manager, E);
  E = NULL;

  /* return the result */
  cuddDeref (res);

  return res;
}

/**
   \brief Recursive part of Ldd_ExistsAbstractFM()
 */

LddNode * 
lddExistsAbstractFMRecur (LddManager * ldd, 
			  LddNode * f, 
			  int var, 
			  DdLocalCache * cache)
{
  DdNode *F, *T, *E;
  
  DdManager * manager;
  
  lincons_t vCons;
  linterm_t vTerm;
  
  DdNode *fv, *fnv;
  unsigned int v;

  DdNode *root;
  DdNode *res;

  /* true if root constraint has to be eliminated, false otherwise */
  int fElimRoot;


  manager = CUDD;
  F = Cudd_Regular (f);
  
  /* base case */
  if (F == DD_ONE(CUDD)) return f;

  /* check cache */
  if (F->ref != 1 && ((res = cuddLocalCacheLookup (cache, &f)) != NULL))
    return res;


  /* deconstruct f into the root constraint and cofactors */
  v = F->index;
  vCons = ldd->ddVars [v];
  vTerm = THEORY->get_term (vCons);
  
  fv = cuddT (F);
  fnv = cuddE (F);

  fv = Cudd_NotCond (fv, f != F);
  fnv = Cudd_NotCond (fnv, f != F);

  /* if variables of vTerm do not contain var, we just recurse.
     otherwise, top constraint is removed and propagated to children
     before recursing to children
  */
  if (!THEORY->term_has_var (vTerm, var))
    {
      /* keep the root constraint */
      fElimRoot = 0;
      /* grab extra references to simplify dereferencing later */
      cuddRef (fv);
      cuddRef (fnv);
    }
  else
    {
      DdNode *tmp;
      lincons_t nvCons;

      /* root constraint is eliminated */
      fElimRoot = 1;

      /* resolve root constraint with THEN branch */
      tmp = lddResolveElimInter (ldd, fv, vTerm, vCons, var);
      if (tmp == NULL)
	{
	  return NULL;
	}      
      cuddRef (tmp);

      fv = tmp;
      
      /* resolve negation of the root constraint with ELSE branch */
      nvCons = THEORY->negate_cons (vCons);
      tmp = lddResolveElimInter (ldd, fnv, vTerm, nvCons, var);
      THEORY->destroy_lincons (nvCons);
      
      if (tmp == NULL)
	{
	  Cudd_IterDerefBdd (manager, fv);
	  return NULL;
	}
      cuddRef (tmp);
      fnv = tmp;
    }
  

  /* recurse to THEN and ELSE branches*/
  T = lddExistsAbstractFMRecur (ldd, fv, var, cache);
  if (T == NULL)
    {
      Cudd_IterDerefBdd (manager, fv);
      Cudd_IterDerefBdd (manager, fnv);
      return NULL;
    }
  cuddRef (T);
  Cudd_IterDerefBdd (manager, fv);
  fv = NULL;
  
  E = lddExistsAbstractFMRecur (ldd, fnv, var, cache);
  if (E == NULL)
    {
      Cudd_IterDerefBdd (manager, T);
      Cudd_IterDerefBdd (manager, fnv);
      return NULL;
    }
  cuddRef (E);
  Cudd_IterDerefBdd (manager, fnv);
  fnv = NULL;

  if (fElimRoot)
    {
      /* do an OR */
      res = lddAndRecur (ldd, Cudd_Not (T), Cudd_Not (E));
      if (res == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  return NULL;
	}
      res = Cudd_Not (res);
      cuddRef (res);
    }
  else
    {
      root = Cudd_bddIthVar (manager, v);
      if (root == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  return NULL;
	}
      cuddRef (root);

      res = lddIteRecur (ldd, root, T, E);
      if (res == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  Cudd_IterDerefBdd (manager, root);
	  return NULL;
	}
      cuddRef (res);
      Cudd_IterDerefBdd (manager, root);
      root = NULL;
    }



  Cudd_IterDerefBdd (manager, T);
  T = NULL;
  Cudd_IterDerefBdd (manager, E);
  E = NULL;

  if (F->ref != 1)
    cuddLocalCacheInsert (cache, &f, res);

  cuddDeref (res);
  return res;
}

/**
   \brief Recursive part of Ldd_ExistsAbstractSFM()
 */
LddNode * 
lddExistsAbstractSFMRecur (LddManager * ldd, 
			     LddNode * f, 
			     int var, 
			  DdLocalCache * cache)
{
  DdNode *F, *T, *E;
  
  DdManager * manager;
  
  lincons_t vCons;
  linterm_t vTerm;
  
  DdNode *fv, *fnv;
  unsigned int v;

  DdNode *root;
  DdNode *res;

  /* true if root constraint has to be eliminated, false otherwise */
  int fElimRoot;

 
  manager = CUDD;
  F = Cudd_Regular (f);
  
  /* base case */
  if (F == DD_ONE(CUDD)) return f;

  /* check cache */
  if (F->ref != 1 && ((res = cuddLocalCacheLookup (cache, &f)) != NULL))
    return res;


  /* deconstruct f into the root constraint and cofactors */
  v = F->index;
  vCons = lddC(ldd,v);
  vTerm = THEORY->get_term (vCons);
  
  fv = cuddT (F);
  fnv = cuddE (F);

  fv = Cudd_NotCond (fv, f != F);
  fnv = Cudd_NotCond (fnv, f != F);

  /* if variables of vTerm do not contain var, we just recurse.
     otherwise, top constraint is removed and propagated to children
     before recursing to children
  */
  fElimRoot = THEORY->term_has_var (vTerm, var);
  if (!fElimRoot)
    {
      /* keep the root constraint */
      /* grab extra references to simplify dereferencing later */
      cuddRef (fv);
      cuddRef (fnv);
    }
  else
    {
      DdNode *tmp;
      lincons_t nvCons;
      
      DdHashTable * resolveTable;

      resolveTable = cuddHashTableInit (CUDD, 1, 2);
      if (resolveTable == NULL) return NULL;

      /* root constraint is eliminated */

      /* resolve root constraint with THEN branch */
      tmp = lddResolveRecur (ldd, fv, vTerm, NULL, vCons, var, resolveTable);
      if (tmp != NULL) cuddRef (tmp);
      cuddHashTableQuit (resolveTable);
      resolveTable = NULL;
      if (tmp == NULL) return NULL;

      fv = tmp;
      
      
      /* resolve negation of the root constraint with ELSE branch */
      resolveTable = cuddHashTableInit (CUDD, 1, 2);
      if (resolveTable == NULL)
	{
	  Cudd_IterDerefBdd (manager, fv);
	  return NULL;
	}
      
      nvCons = THEORY->negate_cons (vCons);
      tmp = lddResolveRecur (ldd, fnv, vTerm, nvCons, NULL, 
			       var, resolveTable);
      THEORY->destroy_lincons (nvCons);

      if (tmp != NULL) cuddRef (tmp);
      cuddHashTableQuit (resolveTable);
      if (tmp == NULL)
	{
	  Cudd_IterDerefBdd (manager, fv);
	  return NULL;
	}
      fnv = tmp;
    }
  

  /* recurse to THEN and ELSE branches*/
  T = lddExistsAbstractSFMRecur (ldd, fv, var, cache);
  if (T == NULL)
    {
      Cudd_IterDerefBdd (manager, fv);
      Cudd_IterDerefBdd (manager, fnv);
      return NULL;
    }
  cuddRef (T);
  Cudd_IterDerefBdd (manager, fv);
  fv = NULL;
  
  E = lddExistsAbstractSFMRecur (ldd, fnv, var, cache);
  if (E == NULL)
    {
      Cudd_IterDerefBdd (manager, T);
      Cudd_IterDerefBdd (manager, fnv);
      return NULL;
    }
  cuddRef (E);
  Cudd_IterDerefBdd (manager, fnv);
  fnv = NULL;

  if (fElimRoot)
    {
      /* do an OR */
      res = lddAndRecur (ldd, Cudd_Not (T), Cudd_Not (E));
      if (res == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  return NULL;
	}
      res = Cudd_Not (res);
      cuddRef (res);
    }
  else
    {
      root = Cudd_bddIthVar (manager, v);
      if (root == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  return NULL;
	}
      cuddRef (root);

      res = lddIteRecur (ldd, root, T, E);
      if (res == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  Cudd_IterDerefBdd (manager, root);
	  return NULL;
	}
      cuddRef (res);
      Cudd_IterDerefBdd (manager, root);
      root = NULL;
    }



  Cudd_IterDerefBdd (manager, T);
  T = NULL;
  Cudd_IterDerefBdd (manager, E);
  E = NULL;

  if (F->ref != 1)
    cuddLocalCacheInsert (cache, &f, res);

  cuddDeref (res);
  return res;
  
}



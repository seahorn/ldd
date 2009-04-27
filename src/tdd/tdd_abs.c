#include "util.h"
#include "tddInt.h"


tdd_node *
tdd_exist_abstract (tdd_manager * tdd,
		    tdd_node * f,
		    int var)
{
  tdd_node *res;
  DdHashTable *table;
  
  do 
    {
      CUDD->reordered = 0;
      table = cuddHashTableInit (CUDD, 1, 2);
      if (table == NULL) return NULL;
      
      res = tdd_exist_abstract_recur (tdd, f, var, table);
      if (res != NULL)
	cuddRef (res);
      cuddHashTableQuit (table);
    } while (CUDD->reordered == 1);
  
  if (res != NULL) cuddDeref (res);
  return res;
}


/**
 * Existential quantification through resolution. Unoptimized version
 * of tdd_exist_abstract.
 */
tdd_node *
tdd_exist_abstract_v3 (tdd_manager * tdd,
		       tdd_node * f,
		       int var)
{
  tdd_node *res;
  DdHashTable *table;
  
  do 
    {
      CUDD->reordered = 0;
      table = cuddHashTableInit (CUDD, 1, 2);
      if (table == NULL) return NULL;
      
      res = tdd_exist_abstract_v3_recur (tdd, f, var, table);
      if (res != NULL)
	cuddRef (res);
      cuddHashTableQuit (table);
    } while (CUDD->reordered == 1);
  
  if (res != NULL) cuddDeref (res);
  return res;
}


tdd_node * tdd_univ_abstract (tdd_manager * tdd,
			      tdd_node * f,
			      int var)
{
  tdd_node *res;
  DdHashTable *table;
  do
    {
      CUDD->reordered = 0;
      table = cuddHashTableInit (CUDD, 1, 2);
      if (table == NULL) return NULL;
      
      res = tdd_exist_abstract_recur (tdd, Cudd_Not (f), var, table);
      if (res != NULL)
	cuddRef (res);
      cuddHashTableQuit (table);
    }
  while (CUDD->reordered == 1);

  if (res != NULL) cuddDeref (res);

  return Cudd_NotCond (res, res != NULL);
}

tdd_node * tdd_resolve_elim (tdd_manager * tdd, tdd_node * f, 
			     linterm_t t, lincons_t cons, int var)
{
  tdd_node *res;
  do
    {
      CUDD->reordered = 0;
      res = tdd_resolve_elim_inter (tdd, f, t, cons, var);
    } 
  while (CUDD->reordered == 1);
  
  return res;

}



tdd_node * tdd_resolve (tdd_manager * tdd, tdd_node * f, 
			linterm_t t, lincons_t negCons, lincons_t posCons, 
			int var)
{
  tdd_node *res;
  DdHashTable *table;


  do
    {
      CUDD->reordered = 0;
      table = cuddHashTableInit (CUDD, 1, 2);
      if (table == NULL) return NULL;
      
      res = tdd_resolve_recur (tdd, f, t, negCons, posCons, var, table);
      if (res != NULL)
	cuddRef (res);
      cuddHashTableQuit (table);
    } 
  while (CUDD->reordered == 1);
  
  if (res != NULL) cuddDeref (res);
  return res;

}

tdd_node *tdd_exist_abstract_v2 (tdd_manager * tdd,
				 tdd_node * f,
				 bool * vars)
{
  tdd_node *res;
  DdHashTable *table;
  qelim_context_t * qelimCtx;
  
  
  do
    {
      CUDD->reordered = 0;

      qelimCtx = THEORY->qelim_init (tdd, vars);
      if (qelimCtx == NULL)
	return NULL;
      
      table = cuddHashTableInit (CUDD, 1, 2);
      if (table == NULL)
	{
	  THEORY->qelim_destroy_context (qelimCtx);
	  return NULL;
	}

      res = tdd_exist_abstract_v2_recur (tdd, f, vars, qelimCtx, table);
      if (res != NULL)
	cuddRef (res);

      THEORY->qelim_destroy_context (qelimCtx);
      cuddHashTableQuit (table);
      
    } while (CUDD->reordered == 1);
  
  if (res != NULL) cuddDeref (res);
  return res;
}


/**
 * Resolve TDD f with constraint 'cons' on variable 'var'. 
 * In the process, eliminates all constraints with the term 't'
 */
tdd_node * tdd_resolve_elim_inter (tdd_manager * tdd, tdd_node * f, 
				   linterm_t t, lincons_t cons, int var)
{
  tdd_node *res;
  bool isNeg;
  

  isNeg = THEORY->is_negative_cons (cons);
  
  /* assert: t is a positive term 
   * cons is either t <= c, t < c or -t <= c, -t < c
   */
  
  res = tdd_resolve_elim_recur (tdd, f, 
				t, 
				isNeg ? cons : NULL, 
				isNeg ? NULL : cons, 
				var);
  return res;
}

/**
 * Recursive part of tdd_exist_abstract
 *
 * table is the hash table to keep computed results of this operation
 */
tdd_node * 
tdd_exist_abstract_recur (tdd_manager * tdd, 
			  tdd_node * f, 
			  int var, 
			  DdHashTable * table)
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
  if (F->ref != 1 && ((res = cuddHashTableLookup1 (table, f)) != NULL))
    return res;


  /* deconstruct f into the root constraint and cofactors */
  v = F->index;
  vCons = tdd->ddVars [v];
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
      tmp = tdd_resolve_elim_inter (tdd, fv, vTerm, vCons, var);
      if (tmp == NULL)
	{
	  return NULL;
	}      
      cuddRef (tmp);

      fv = tmp;
      
      
      /* resolve negation of the root constraint with ELSE branch */
      nvCons = THEORY->negate_cons (vCons);
      tmp = tdd_resolve_elim_inter (tdd, fnv, vTerm, nvCons, var);
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
  T = tdd_exist_abstract_recur (tdd, fv, var, table);
  if (T == NULL)
    {
      Cudd_IterDerefBdd (manager, fv);
      Cudd_IterDerefBdd (manager, fnv);
      return NULL;
    }
  cuddRef (T);
  Cudd_IterDerefBdd (manager, fv);
  fv = NULL;
  
  E = tdd_exist_abstract_recur (tdd, fnv, var, table);
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
      res = tdd_and_recur (tdd, Cudd_Not (T), Cudd_Not (E));
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

      res = tdd_ite_recur (tdd, root, T, E);
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
    {
      ptrint fanout = (ptrint) F->ref;
      cuddSatDec (fanout);
      if (!cuddHashTableInsert1 (table, f, res, fanout))
	{
	  Cudd_IterDerefBdd (CUDD, res);
	  return NULL;
	}
    }
  
  cuddDeref (res);
  return res;
  
}

/**
 * Recursive part of tdd_exist_abstract_v3
 *
 * table is the hash table to keep computed results of this operation
 */
tdd_node * 
tdd_exist_abstract_v3_recur (tdd_manager * tdd, 
			     tdd_node * f, 
			     int var, 
			     DdHashTable * table)
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
  if (F->ref != 1 && ((res = cuddHashTableLookup1 (table, f)) != NULL))
    return res;


  /* deconstruct f into the root constraint and cofactors */
  v = F->index;
  vCons = tdd->ddVars [v];
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
      tmp = tdd_resolve (tdd, fv, vTerm, NULL, vCons, var);
      if (tmp == NULL)
	{
	  return NULL;
	}      
      cuddRef (tmp);

      fv = tmp;
      
      
      /* resolve negation of the root constraint with ELSE branch */
      nvCons = THEORY->negate_cons (vCons);
      tmp = tdd_resolve (tdd, fv, vTerm, nvCons, NULL, var);
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
  T = tdd_exist_abstract_v3_recur (tdd, fv, var, table);
  if (T == NULL)
    {
      Cudd_IterDerefBdd (manager, fv);
      Cudd_IterDerefBdd (manager, fnv);
      return NULL;
    }
  cuddRef (T);
  Cudd_IterDerefBdd (manager, fv);
  fv = NULL;
  
  E = tdd_exist_abstract_v3_recur (tdd, fnv, var, table);
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
      res = tdd_and_recur (tdd, Cudd_Not (T), Cudd_Not (E));
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

      res = tdd_ite_recur (tdd, root, T, E);
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
    {
      ptrint fanout = (ptrint) F->ref;
      cuddSatDec (fanout);
      if (!cuddHashTableInsert1 (table, f, res, fanout))
	{
	  Cudd_IterDerefBdd (CUDD, res);
	  return NULL;
	}
    }
  
  cuddDeref (res);
  return res;
  
}


/**
 * Recursive part of tdd_resolve_elim
 *
 * Parameters:
 *  tdd          TDD manager
 *  f            the target of resolution/elimination
 *  t            the (positive) term being eliminted
 *  negCons      negative constraint (lower bound) of the form -t <= lower
 *  posCons      positive constraint (upper bound) of the form  t <= upper
 *  var          variable being eliminated and resolved on
 *
 * Requires:
 *  1. var has a non-zero coefficient in t
 *  2. negCons is NULL or of the form  -t <= lower or -t < lower
 *  3. posCons is NULL or of the form   t <= upper or t < upper
 *
 */
tdd_node *tdd_resolve_elim_recur (tdd_manager * tdd,
				  tdd_node * f,
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
      tdd_node * r;
      
      table = cuddHashTableInit (CUDD, 1, 2);
      if (table == NULL) return NULL;

      r = tdd_resolve_recur (tdd, f, t, negCons, posCons, var, table);

      if (r != NULL) cuddRef (r);
      cuddHashTableQuit (table);
      if (r != NULL) cuddDeref (r);

      return r;
    }
  


  /* assert: posCons == NULL && negCons != NULL */


  /* get index and constraint of the root node */
  v = F->index;
  vCons = tdd->ddVars [v];
  vTerm = THEORY->get_term (vCons);


  /* terminal case. bounds cannot change. */
  if (!THEORY->term_equals (vTerm, t))
    {
      DdHashTable* table;
      tdd_node * r;

      table = cuddHashTableInit (CUDD, 1, 2);
      if (table == NULL) return NULL;      

      r = tdd_resolve_recur (tdd, f, t, negCons, posCons, var, table);

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
  T = tdd_resolve_elim_recur (tdd, fv, t, negCons, vCons, var);
  if (T == NULL) return NULL;
  cuddRef (T);
  
  {
    lincons_t nvCons = THEORY->negate_cons (vCons);
    E = tdd_resolve_elim_recur (tdd, fnv, t, nvCons, (lincons_t)NULL, var);  
    THEORY->destroy_lincons (nvCons);
  }
  

  if (E == NULL) 
    {
      Cudd_IterDerefBdd (manager, T);
      return NULL;
    }
  cuddRef (E);

  res = tdd_and_recur (tdd, Cudd_Not(T), Cudd_Not(E));
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
 * Recursive part of tdd_resolve. Resolves negCons and posCons with
 * TDD f.  t is the term of posCons and -t is the term of negCons. var
 * is the resolution variable. table is the hashtable to keep computed
 * results.
 */
tdd_node *
tdd_resolve_recur (tdd_manager * tdd,
		   tdd_node * f,
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
  vCons = tdd->ddVars [v];
  vTerm = THEORY->get_term (vCons);
  
  /* get THEN and ELSE branches */
  fv = cuddT (F);
  fnv = cuddE (F);  

  /* compute cofactors */
  fv = Cudd_NotCond (fv, f != F);
  fnv = Cudd_NotCond (fnv, f != F);


  /** recursive call */
  T = tdd_resolve_recur (tdd, fv, t, negCons, posCons, var, table);
  if (T == NULL) return NULL;
  cuddRef (T);

  /* recursive call */
  E = tdd_resolve_recur (tdd, fnv, t, negCons, posCons, var, table);  
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
     
      c = THEORY->to_tdd (tdd, tCons);
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
      
	
      tmp = tdd_and_recur (tdd, c, T);
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

      c = THEORY->to_tdd (tdd, eCons);
      THEORY->destroy_lincons (eCons);
      eCons = NULL;
      
      if (c == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  return NULL;
	}
      cuddRef (c);
            
      tmp = tdd_and_recur (tdd, c, E);
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

  res = tdd_ite_recur (tdd, root, T, E);
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


tdd_node * tdd_exist_abstract_v2_recur (tdd_manager * tdd, 
					tdd_node * f, 
					bool * vars, 
					qelim_context_t * qelimCtx,
					/* table is unused for now */
					DdHashTable * table)
{
  DdNode *one, *zero;
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
  one = DD_ONE (manager);
  zero = Cudd_Not (one);
  
  
  /* base case */
  if (f == one)
    {
      tdd_node *sol;
      
/*       printf ("QELIM TERMINATION:\n"); */
      sol = THEORY->qelim_solve (qelimCtx);
      return sol;
    }
  

  if (f == zero) return zero;

  /* XXX uqly way to check for satisfiability */
  res = THEORY->qelim_solve (qelimCtx);
  if (res == zero) 
    {
/*       printf ("EARLY TERMINATION:\n"); */
      return zero;
    }
  
  
  /* if res is not zero, need to clean it properly by first 
     getting a reference to it, and then dropping it */
  cuddRef (res);
  Cudd_IterDerefBdd (manager, res);
  

  /* deconstruct f into the root constraint and cofactors */
  F = Cudd_Regular (f);
  v = F->index;
  vCons = tdd->ddVars [v];
  vTerm = THEORY->get_term (vCons);
  
  fv = cuddT (F);
  fnv = cuddE (F);
  
  fv = Cudd_NotCond (fv, f != F);
  fnv = Cudd_NotCond (fnv, f != F);



  /* XXX MISSING OPTIMIZATION:
   *
   * if qelimCtx && vCons is UNSAT, only need to proceed with qelimCtx
   * on the ELSE branch of the diagram. The THEN part and vCons can be
   * dropped.
   *
   * if qelimCtx && !vCons is UNSAT, only need to proceed with
   * qelimCtx on the THEN branch of the diagram. The ELSE part and
   * vCons can be dropped
   */


  fElimRoot = THEORY->term_has_vars (vTerm, vars);


  /* recurse on the THEN branch*/
  if (fElimRoot)
    {
      THEORY->qelim_push (qelimCtx, vCons);
    }
  

  T = tdd_exist_abstract_v2_recur (tdd, fv, vars, qelimCtx, table);

  if (fElimRoot) 
    THEORY->qelim_pop (qelimCtx);
  
  if (T == NULL)
    {
/*       Cudd_IterDerefBdd (manager, fv); */
/*       Cudd_IterDerefBdd (manager, fnv); */
      return NULL;
    }
  cuddRef (T);
/*   Cudd_IterDerefBdd (manager, fv); */
  fv = NULL;


  /* recurs on the ELSE branch */
  if (fElimRoot)
    {
      lincons_t nvCons;
      nvCons = THEORY->negate_cons (vCons);
      THEORY->qelim_push (qelimCtx, nvCons);
    }    

  E = tdd_exist_abstract_v2_recur (tdd, fnv, vars, qelimCtx, table);

  if (fElimRoot)
    THEORY->destroy_lincons (THEORY->qelim_pop (qelimCtx));

  if (E == NULL)
    {
      Cudd_IterDerefBdd (manager, T);
/*       Cudd_IterDerefBdd (manager, fnv); */
      return NULL;
    }
  cuddRef (E);
/*   Cudd_IterDerefBdd (manager, fnv); */
  fnv = NULL;

  if (!fElimRoot)
    {
      root = Cudd_bddIthVar (manager, v);
      if (root == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  return NULL;
	}
      cuddRef (root);

      res = tdd_ite_recur (tdd, root, T, E);
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
  else
    {
      res = tdd_and_recur (tdd, Cudd_Not (T), Cudd_Not (E));
      if (res == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  return NULL;
	}
      res = Cudd_Not (res);
      cuddRef (res);
    }
  Cudd_IterDerefBdd (manager, T);
  T = NULL;
  Cudd_IterDerefBdd (manager, E);
  E = NULL;

/*   if (F->ref != 1) */
/*     { */
/*       ptrint fanout = (ptrint) F->ref; */
/*       cuddSatDec (fanout); */
/*       if (!cuddHashTableInsert1 (table, f, res, fanout)) */
/* 	{ */
/* 	  Cudd_IterDerefBdd (CUDD, res); */
/* 	  return NULL; */
/* 	} */
/*     } */
  
  cuddDeref (res);
  return res;
  
}

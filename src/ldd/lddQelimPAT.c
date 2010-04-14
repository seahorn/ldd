/**
   Path-At-a-Time quantifier elimination using an external quantifier
   elimination for conjunctions of constraints.
 */
#include "util.h"
#include "lddInt.h"


/**
   \brief Existential quantifies out variables from a diagram using
   Path-At-a-Time technique.

   \param ldd Ldd manager

   \param f an LDD from which variables are quantified

   \param vars a Boolean array indicating which variables are
   quantified out. 1 at location i means that ith variable is
   quantified out

   
   
   
   \pre Theory implements quantifier elimination interface. vars is at
   least as large as number of variables in the theory.
   
 */
LddNode *
Ldd_ExistAbstractPAT (LddManager * ldd,
		      LddNode * f,
		      bool * vars)
{
  LddNode *res;
  DdHashTable *table;
  qelim_context_t * qelimCtx;
  
  
  do
    {
      CUDD->reordered = 0;

      qelimCtx = THEORY->qelim_init (ldd, vars);
      if (qelimCtx == NULL)
	return NULL;
      
      table = cuddHashTableInit (CUDD, 1, 2);
      if (table == NULL)
	{
	  THEORY->qelim_destroy_context (qelimCtx);
	  return NULL;
	}

      res = lddExistAbstractPATRecur (ldd, f, vars, qelimCtx, table);
      if (res != NULL)
	cuddRef (res);

      THEORY->qelim_destroy_context (qelimCtx);
      cuddHashTableQuit (table);
      
    } while (CUDD->reordered == 1);
  
  if (res != NULL) cuddDeref (res);
  return res;
}





/**
   \brief Recursive version of Ldd_ExistAbstractPAT()
 */
LddNode * 
lddExistAbstractPATRecur (LddManager * ldd, 
			  LddNode * f, 
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
      LddNode *sol;
      
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
  vCons = ldd->ddVars [v];
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
  

  T = lddExistAbstractPATRecur (ldd, fv, vars, qelimCtx, table);

  if (fElimRoot) 
    THEORY->qelim_pop (qelimCtx);
  
  if (T == NULL) return NULL;
  cuddRef (T);
  fv = NULL;


  /* recurs on the ELSE branch */
  if (fElimRoot)
    {
      lincons_t nvCons;
      nvCons = THEORY->negate_cons (vCons);
      THEORY->qelim_push (qelimCtx, nvCons);
    }    

  E = lddExistAbstractPATRecur (ldd, fnv, vars, qelimCtx, table);

  if (fElimRoot)
    THEORY->destroy_lincons (THEORY->qelim_pop (qelimCtx));

  if (E == NULL)
    {
      Cudd_IterDerefBdd (manager, T);
      return NULL;
    }
  cuddRef (E);
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
  else
    {
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
  Cudd_IterDerefBdd (manager, T);
  T = NULL;
  Cudd_IterDerefBdd (manager, E);
  E = NULL;

  cuddDeref (res);
  return res;
  
}

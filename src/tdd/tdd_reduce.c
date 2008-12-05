#include "util.h"
#include "tddInt.h"


/**
 * Reduces a TDD by removing all unsatisfiable paths of length less
 * than or equal to 'depth'. When depth is less than 0, removes paths
 * of arbitrary length.
 */
tdd_node *
tdd_sat_reduce (tdd_manager *tdd, 
		tdd_node *f,
		int depth)
{
  tdd_node *res;
  qelim_context_t *ctx;
  bool * vars;
  int i, n;
  

  n = THEORY->num_of_vars (THEORY);
  vars = ALLOC (bool, n);
  if (vars == NULL) return NULL;
  
  for (i = 0; i < n; i++)
    vars [i] = 1;
  
  
  ctx = THEORY->qelim_init (tdd, vars);

  if (ctx == NULL)
    {
      FREE (vars);
      return NULL;
    }

  do {
    CUDD->reordered = 0;
    res = tdd_sat_reduce_recur (tdd, f, ctx, depth);
    if (res != NULL)
      cuddRef (res);
  } while (CUDD->reordered == 1);


  if (ctx)
    {
      THEORY->qelim_destroy_context (ctx);
      ctx = NULL;
    }

  if (vars)
    {
      FREE (vars);
      vars = NULL;
    }
  

  if (res != NULL)
    cuddDeref (res);
  return res;
}


tdd_node *
tdd_sat_reduce_recur (tdd_manager *tdd, 
		      tdd_node *f,
		      qelim_context_t * ctx,
		      int depth)
{
  tdd_node *F, *t, *e;

  tdd_node *fv, *fnv;
  
  tdd_node *tmp;
  
  unsigned int v;
  lincons_t vCons, nvCons;
  
  tdd_node *root;
  tdd_node *res;

  tdd_node *zero;

/* reached our limit */
  if (depth == 0) return f;
  
  F = Cudd_Regular (f);
  
  /* terminal constant */
  if (F == DD_ONE(CUDD)) return f;


  zero = Cudd_Not (DD_ONE (CUDD));
  v = F->index;
  vCons = tdd->ddVars [v];

  fv = Cudd_NotCond (cuddT (F), f != F);
  fnv = Cudd_NotCond (cuddE (F), f != F);

  t = e = NULL;


  THEORY->qelim_push (ctx, vCons);

  tmp = THEORY->qelim_solve (ctx);
  if (tmp == NULL) return NULL;

  if (tmp != zero)
    {
      cuddRef (tmp);
      Cudd_IterDerefBdd (CUDD, tmp);

      t = tdd_sat_reduce_recur (tdd, fv, ctx, depth - 1);
      
      if (t == NULL)
	return NULL;

      cuddRef (t);
    }
/*   else */
/*     printf ("INCONSISTENT THEN\n"); */

  THEORY->qelim_pop (ctx);
  tmp = NULL;
  

  nvCons = THEORY->negate_cons (vCons);
  THEORY->qelim_push (ctx, nvCons);
  tmp = THEORY->qelim_solve (ctx);

  if (tmp == NULL)
    {
      Cudd_IterDerefBdd (CUDD, t);
      THEORY->destroy_lincons (THEORY->qelim_pop (ctx));
      return NULL;
    }

  if (tmp != zero)
    {
      cuddRef (tmp);
      Cudd_IterDerefBdd (CUDD, tmp);
      
      e = tdd_sat_reduce_recur (tdd, fnv, ctx, depth - 1);
      
      if (e == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  THEORY->destroy_lincons (THEORY->qelim_pop (ctx));
	  return NULL;
	}
      cuddRef (e);
    }
/*   else */
/*     printf ("INCONSISTENT ELSE\n"); */

  THEORY->destroy_lincons (THEORY->qelim_pop (ctx));
  
  /* only one of T and E can be NULL */
  if (t == NULL || e == NULL)
    res = (t != NULL) ? t : e;
  
  else if (t == e)
    {
      res = t;

      cuddDeref (e);  
      e = NULL;
    }
  else
    {      
      root = Cudd_bddIthVar (CUDD, v);

      if (root == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  Cudd_IterDerefBdd (CUDD, e);
	  return NULL;
	}
      cuddRef (root);

      res = tdd_ite_recur (tdd, root, t, e);

      if (res != NULL)
	cuddRef (res);

      Cudd_IterDerefBdd (CUDD, t);
      t = NULL;
      Cudd_IterDerefBdd (CUDD, e);
      e = NULL;
      Cudd_IterDerefBdd (CUDD, root);
      root = NULL;
    }
  
  if (res != NULL)
    cuddDeref (res);
  return res;
  
}


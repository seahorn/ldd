#include "util.h"
#include "tddInt.h"


static int Ldd_unsat_size_recur (LddManager *ldd, LddNode *f);
static void lddClearFlag (LddNode *f);


/**
 * Reduces a LDD by removing all unsatisfiable paths of length less
 * than or equal to 'depth'. When depth is less than 0, removes paths
 * of arbitrary length.
 */
LddNode *
Ldd_SatReduce (LddManager *ldd, 
		LddNode *f,
		int depth)
{
  LddNode *res;
  qelim_context_t *ctx;
  bool * vars;
  int i, n;
  

  n = THEORY->num_of_vars (THEORY);
  vars = ALLOC (bool, n);
  if (vars == NULL) return NULL;
  
  for (i = 0; i < n; i++)
    vars [i] = 1;
  
  
  ctx = THEORY->qelim_init (ldd, vars);

  if (ctx == NULL)
    {
      FREE (vars);
      return NULL;
    }

  do {
    CUDD->reordered = 0;
    res = Ldd_sat_reduce_recur (ldd, f, ctx, depth);
    if (res != NULL)
      cuddRef (res);
  } while (CUDD->reordered == 1);


  THEORY->qelim_destroy_context (ctx);
  ctx = NULL;
  FREE (vars);
  vars = NULL;
  

  if (res != NULL)
    cuddDeref (res);
  return res;
}


/**
   returns true if f is satisfiable, false if it isn't */
bool
Ldd_IsSat (LddManager *ldd,
	    LddNode *f)
{
  bool res;
  qelim_context_t *ctx;
  bool * vars;
  int i, n;
  

  n = THEORY->num_of_vars (THEORY);
  vars = ALLOC (bool, n);
  if (vars == NULL) return 0;
  
  for (i = 0; i < n; i++)
    vars [i] = 1;
  
  
  ctx = THEORY->qelim_init (ldd, vars);

  if (ctx == NULL)
    {
      FREE (vars);
      return 0;
    }

  res = Ldd_is_sat_recur (ldd, f, ctx);
  
  THEORY->qelim_destroy_context (ctx);
  ctx = NULL;
  FREE (vars);
  vars = NULL;

  return res;
  
}


LddNode *
Ldd_sat_reduce_recur (LddManager *ldd, 
		      LddNode *f,
		      qelim_context_t * ctx,
		      int depth)
{
  LddNode *F, *t, *e;

  LddNode *fv, *fnv;
  
  LddNode *tmp;
  
  unsigned int v;
  lincons_t vCons, nvCons;
  
  LddNode *root;
  LddNode *res;

  LddNode *zero;

/* reached our limit */
  if (depth == 0) return f;
  
  F = Cudd_Regular (f);
  
  /* terminal constant */
  if (F == DD_ONE(CUDD)) return f;


  zero = Cudd_Not (DD_ONE (CUDD));
  v = F->index;
  vCons = ldd->ddVars [v];

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

      t = Ldd_sat_reduce_recur (ldd, fv, ctx, depth - 1);
      
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
      
      e = Ldd_sat_reduce_recur (ldd, fnv, ctx, depth - 1);
      
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

      res = Ldd_ite_recur (ldd, root, t, e);

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

bool
Ldd_is_sat_recur (LddManager *ldd, 
		  LddNode *f, 
		  qelim_context_t * ctx)
{

  LddNode *zero;

  
  LddNode *F, *fnv, *fv;
  LddNode *tmp;
  
  unsigned int v;
  lincons_t vCons, nvCons;
  int res;

  
  zero = Cudd_Not (DD_ONE(CUDD));

  if (Cudd_IsConstant (f)) return f == DD_ONE (CUDD);

  F = Cudd_Regular (f);
  v = F->index;
  vCons = ldd->ddVars [v];
  

  fv = Cudd_NotCond (cuddT (F), f != F);
  fnv = Cudd_NotCond (cuddE (F), f != F);
  
  THEORY->qelim_push (ctx, vCons);
  tmp = THEORY->qelim_solve (ctx);
  

  /* if ctx && vCons is UNSAT. Then ctx implies !vCons. Hence, don't
     need to add !vCons to the context, and only need to explore the
     ELSE branch */
  if (tmp == zero)
    {
      THEORY->qelim_pop (ctx);
      return Ldd_is_sat_recur (ldd, fnv, ctx);
    }

  assert (tmp == DD_ONE (CUDD));

  res = Ldd_is_sat_recur (ldd, fv, ctx);
  THEORY->qelim_pop (ctx);
  
  /* THEN branch is SAT, we are done */
  if (res) return res;
  
  /* check ELSE branch */
  nvCons = THEORY->negate_cons (vCons);
  THEORY->qelim_push (ctx, nvCons);
  tmp = THEORY->qelim_solve (ctx);

  /* !vCons contradicts with the context */
  if (tmp == zero) 
    {
      THEORY->qelim_pop (ctx);
      THEORY->destroy_lincons (nvCons);
      return 0;
    }
  
  assert (tmp == DD_ONE(CUDD));
  
  res = Ldd_is_sat_recur (ldd, fnv, ctx);
  THEORY->qelim_pop (ctx);
  THEORY->destroy_lincons (nvCons);

  return res;
}

int
Ldd_UnsatSize(LddManager *ldd, 
		LddNode *f)
{
  int i;
  
  i = Ldd_unsat_size_recur (ldd, f);
  lddClearFlag (Cudd_Regular (f));
  return i;
}


static int
Ldd_unsat_size_recur (LddManager *ldd, 
		      LddNode *f)
{
  LddNode *F;
  int tval, eval;
  int r;

  F = Cudd_Regular (f);

  if (Cudd_IsComplement (F->next)) return 0;
  
  F->next = Cudd_Not (F->next);
  
  if (cuddIsConstant (F)) return 0;
  
  tval = Ldd_unsat_size_recur (ldd, Cudd_NotCond (cuddT (F), f != F));
  eval = Ldd_unsat_size_recur (ldd, Cudd_NotCond (cuddE (F), f != F));
  
  r = Ldd_IsSat (ldd, f) ? 0 : 1;

  if (r == 1) 
    {
      fprintf (stdout, "UNSAT SUBTREE\n");
      fflush (stdout);
    }
/*   else */
/*     { */
/*       fprintf (stdout, "SAT SUBTREE\n"); */
/*       fflush (stdout); */
/*     } */
  
  
  return  r + tval + eval;
}


static void 
lddClearFlag (LddNode *f)
{
  if (!Cudd_IsComplement (f->next)) return;
  
  f->next = Cudd_Regular (f->next);
  
  if (cuddIsConstant (f)) return;

  lddClearFlag (cuddT(f));
  lddClearFlag (Cudd_Regular (cuddE (f)));
}

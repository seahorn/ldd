/** Quantifier elimination using The Methods of Infinitesimals by Loos
    and Weispfenning 
*/
#include "util.h"
#include "tddInt.h"

static LddNode *
lddSubstFnForVar (LddManager *ldd,
		  LddNode *f,
		  int var,
		  LddNode*(*fn)(LddManager*,lincons_t,int,
				linterm_t,constant_t),
		  linterm_t t,
		  constant_t c);
static LddNode *
lddSubstFnForVarRecur (LddManager *ldd,
		       LddNode *f,
		       int var,
		       LddNode*(*fn)(LddManager*,lincons_t,int,
				     linterm_t,constant_t),
		       linterm_t t,
		       constant_t c,
		       DdHashTable *table);



LddNode *
Ldd_SubstNinfForVar (LddManager *ldd,
		    LddNode *f,
		    int var)
{
  LddNode *res;
  DdHashTable *table;
  
  do
    {
      CUDD->reordered = 0;
      table = cuddHashTableInit (CUDD, 1, 2);
      
      res = lddSubstNinfForVarRecur (ldd, f, var, table);
      if (res != NULL)
	cuddRef (res);
      cuddHashTableQuit (table);
    }
  while (CUDD->reordered == 1);

  if (res != NULL) cuddDeref (res);
  return res;
}

LddNode * Ldd_SubstTermForVar (LddManager *ldd,
			       LddNode *f,
			       int var, 
			       linterm_t t, 
			       constant_t c)
{
  return lddSubstFnForVar (ldd, f, var, THEORY->subst, t, c);
}

LddNode * 
Ldd_SubstTermPlusForVar (LddManager *ldd,
				   LddNode *f,
				   int var,
				   linterm_t t,
				   constant_t c)
{
  return lddSubstFnForVar (ldd, f, var, THEORY->subst_pluse, t, c);
}


static LddNode *
lddSubstFnForVar (LddManager *ldd,
		  LddNode *f,
		  int var,
		  LddNode*(*fn)(LddManager*,lincons_t,int,
				linterm_t,constant_t),
		  linterm_t t,
		  constant_t c)
{
  LddNode *res;
  DdHashTable *table;
  
  do
    {
      CUDD->reordered = 0;
      table = cuddHashTableInit (CUDD, 1, 2);
      
      res = lddSubstFnForVarRecur (ldd, f, var, fn, t, c, table);
      if (res != NULL)
	cuddRef (res);
      cuddHashTableQuit (table);
    }
  while (CUDD->reordered == 1);

  if (res != NULL) cuddDeref (res);
  return res;  
}

LddNode *
Ldd_ExistsAbstractLW (LddManager *ldd,
		      LddNode *f,
		      int var)
{
  LddNode *res;
  int *support;
  size_t size;
  int i;
  
  res = Ldd_SubstNinfForVar (ldd, f, var);

  /* if nothing changes, then f has no constraints with x */
  if (res == f) return res;

  cuddRef (res);
  
  /* get index of all constraints that occur in the diagram */
  size = ldd->cudd->size;
  support = Cudd_SupportIndex (CUDD, f);
  if (support == NULL) 
    {
      Cudd_IterDerefBdd (CUDD, res);
      return NULL;
    }
  


  for (i = 0; i < size; i++)
    {
      lincons_t l;
      linterm_t t;
      constant_t c; 
      int sgn;

      LddNode *g, *tmp;

      
      fprintf (stderr, "%d iteration of LW\n", i);

      /* skip empty entries */
      if (support [i] == 0) continue;
      l = lddC (ldd, i);

      /* skip non-constraint entries */
      if (l == NULL) continue;

      /* skip constraints that don't depend on var */
      if (!THEORY->term_has_var (THEORY->get_term (l), var)) continue;
      
      
      THEORY->var_bound (l, var, &t, &c);
      sgn = THEORY->sgn_cst (THEORY->var_get_coeff (THEORY->get_term (l), var));

      if ((THEORY->is_strict (l) && sgn > 0) || 
	  (!THEORY->is_strict (l) && sgn < 0))
	g = Ldd_SubstTermForVar (ldd, f, var, t, c);
      else
	g = Ldd_SubstTermPlusForVar (ldd, f, var, t, c);

      THEORY->destroy_term (t);
      THEORY->destroy_cst (c);

      if (g == NULL) 
	{
	  Cudd_IterDerefBdd (CUDD, res);
	  return NULL;
	}
      cuddRef (g);
      
      tmp = Ldd_Or (ldd, res, g);
      if (tmp == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, g);
	  Cudd_IterDerefBdd (CUDD, res);
	  return NULL;
	}
      cuddRef (tmp);
      Cudd_IterDerefBdd (CUDD, res);
      Cudd_IterDerefBdd (CUDD, g);
      res = tmp;
    }
  
  cuddDeref (res);
  return res;
}


LddNode *
lddSubstNinfForVarRecur (LddManager * ldd, 
			 LddNode * f, 
			 int var, 
			 DdHashTable *table)
{
  DdNode *F;
  DdNode *res;
  
  lincons_t lCons;
  
  F = Cudd_Regular (f);
  
  if (F == DD_ONE(CUDD)) return f;

  if (F->ref != 1 && ((res = cuddHashTableLookup1 (table, F)) != NULL))
    return Cudd_NotCond (res, f != F);



  lCons = lddC (ldd, F->index);
  if (THEORY->term_has_var (THEORY->get_term (lCons), var))
    {
      if (THEORY->subst_ninf (ldd, lCons, var) == DD_ONE(CUDD))
	res = lddSubstNinfForVarRecur (ldd, cuddT (F), var, table);
      else
	res = lddSubstNinfForVarRecur (ldd, cuddE (F), var, table);
      if (res == NULL) return NULL;
      cuddRef (res);
    }
  else 
    {
      DdNode *t, *e;
      t = lddSubstNinfForVarRecur (ldd, cuddT (F), var, table);
      if (t == NULL) return NULL;
      cuddRef (t);
      
      e = lddSubstNinfForVarRecur (ldd, cuddE (F), var, table);
      if (e == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  return NULL;
	}
      cuddRef (e);
      
      if (t == e)
	res = t;
      else
	{
	  if (Cudd_IsComplement (t))
	    {
	      res = 
		Ldd_unique_inter (ldd, F->index, Cudd_Not (t), Cudd_Not (e));
	      if (res == NULL)
		{
		  Cudd_IterDerefBdd (CUDD, t);
		  Cudd_IterDerefBdd (CUDD, e);
		  return NULL;
		}
	      res = Cudd_Not (res);
	    }
	  else
	    {
	      res = Ldd_unique_inter (ldd, F->index, t, e);
	      if (res == NULL)
		{
		  Cudd_IterDerefBdd (CUDD, t);
		  Cudd_IterDerefBdd (CUDD, e);
		  return NULL;
		}
	    }
	}
      cuddRef (res);
      Cudd_IterDerefBdd (CUDD, t);
      Cudd_IterDerefBdd (CUDD, e);      
    }
  
  
  if (F->ref != 1)
    {
      ptrint fanout = (ptrint) F->ref;
      cuddSatDec (fanout);
      if (!cuddHashTableInsert1 (table, F, res, fanout))
	{
	  Cudd_IterDerefBdd (CUDD, res);
	  return NULL;
	}
    }

  cuddDeref (res);
  return Cudd_NotCond (res, f != F);
}


static LddNode *
lddSubstFnForVarRecur (LddManager *ldd,
		       LddNode *f,
		       int var,
		       LddNode*(*fn)(LddManager*,lincons_t,int,
				     linterm_t,constant_t),
		       linterm_t term,
		       constant_t cst,
		       DdHashTable *table)
{
  DdNode *F, *res;
  DdNode *one, *zero;
  
  
  DdNode *root;
  lincons_t lCons;
  
  one = DD_ONE(CUDD);
  zero = Cudd_Not (one);
  

  F = Cudd_Regular (f);
  if (F == one) return f;
  
  if (F->ref != 1 && ((res = cuddHashTableLookup1 (table, F)) != NULL))
    return Cudd_NotCond (res, f != F);


  lCons = lddC (ldd, F->index);
  if (THEORY->term_has_var (THEORY->get_term (lCons), var))
    root = fn (ldd, lCons, var, term, cst);
  else
    root = Cudd_bddIthVar (CUDD, F->index);

  if (root == NULL) return NULL;
  cuddRef (root);

  if (root == one || root == zero)
    {
      DdNode *fi = root == one ? cuddT (F) : cuddE (F);
      res = lddSubstFnForVarRecur (ldd, fi, var, fn, term, cst, table);
      if (res == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, root);
	  return NULL;
	}
      cuddRef (res);
    }
  else
    {
      DdNode *t, *e;
      t = lddSubstFnForVarRecur (ldd, cuddT (F), var, fn, term, cst, table);
      if (t == NULL) 
	{
	  Cudd_IterDerefBdd (CUDD, root);
	  return NULL;
	}
      cuddRef (t);

      e = lddSubstFnForVarRecur (ldd, cuddE (F), var, fn, term, cst, table);
      if (e == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, root);
	  Cudd_IterDerefBdd (CUDD, t);
	  return NULL;
	}
      cuddRef (e);
      
      res = Ldd_ite_recur (ldd, root, t, e);
      if (res == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, root);
	  Cudd_IterDerefBdd (CUDD, t);
	  Cudd_IterDerefBdd (CUDD, e);
	  return NULL;
	}
      cuddRef (res);
    
      Cudd_IterDerefBdd (CUDD, t);
      Cudd_IterDerefBdd (CUDD, e);
    }
  Cudd_IterDerefBdd (CUDD, root);

  if (F->ref != 1)
    {
      ptrint fanout = (ptrint) F->ref;
      cuddSatDec (fanout);
      if (!cuddHashTableInsert1 (table, F, res, fanout))
	{
	  Cudd_IterDerefBdd (CUDD, res);
	  return NULL;
	}
    }

  cuddDeref (res);
  return Cudd_NotCond (res, f != F);
}


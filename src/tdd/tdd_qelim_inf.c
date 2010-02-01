/** Quantifier elimination using The Methods of Infinitesimals by Loos
    and Weispfenning 
*/


LddNode *
Ldd_SubsNinfForVar (LddManager *ldd,
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


Ldd_Node*
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
  size = ldd->varsSize;
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

      

      /* skip empty entries */
      if (support [i] == 0) continue;
      l = tddC (ldd, i);
      
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
	  Cudd_IterDerefBdd (ldd, g);
	  Cudd_IterDerefBdd (ldd, res);
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
  DdNode *zero;
  
  lincons_t lCons;
  
  F = Cudd_Regular (f);
  
  if (f == DD_ONE(CUDD)) return f;

  if (F->ref != 1 && ((res = cuddHashTableLookup1 (table, F)) != NULL))
    return Cudd_NotCond (res, f != F);


  zero = Cudd_Not (DD_ONE(CUDD));

  lCons = lddC (ldd, F->index);
  if (THEORY->term_has_var (THEORY->get_term (lCons)), var)
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
      t = lddSubstNinfForVarRecur (ldd, f1, var, table);
      if (t == NULL) return NULL;
      cuddRef (t);
      
      e = lddSubstNinfForVarRecur (ldd, f0, var, table);
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


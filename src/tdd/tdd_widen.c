#include "util.h"
#include "tddInt.h"



/** 
 * Extrapolation for intervals. 
 * Extrapolates f by g. Assumes that f IMPLIES g
 * Untested, unproven, use at your own risk 
 */
tdd_node * 
tdd_box_extrapolate (tdd_manager *tdd, tdd_node *f, tdd_node *g)
{
  tdd_node *res;
  
  do 
    {
      CUDD->reordered = 0;
      res = tdd_box_extrapolate_recur (tdd, f, g);
    } while (CUDD->reordered == 1);
  return (res);
}

/**
 * Apply t1 <- a*t2 + [kmin,kmax], i.e, replace all
 * constraints on term t1 with a linear combination on constraints
 * with term t2.
 *
 * t2 can be NULL, in which case a is ignored
 * kmin == NULL means kmin is negative infinity
 * kmax == NULL means kmax is positive infinity
 */
tdd_node * 
tdd_term_replace (tdd_manager *tdd, tdd_node *f, linterm_t t1, 
		  linterm_t t2, constant_t a, constant_t kmin, constant_t kmax)
{
  tdd_node *res;
  DdHashTable * table;

  /* local copy of t2 */
  linterm_t lt2;
  /* local copy of a */
  constant_t la;
  

  /* if (t2 != NULL) then a != NULL */
  assert (t2 == NULL || a != NULL);
  /* if t2 != NULL then at least one of kmin or kmax is not NULL */
  assert (t2 == NULL || (kmin != NULL || kmax != NULL));
  
  /* simplify */
  if (a != NULL && THEORY->is_zero_cst (a))
    {
      lt2 = NULL;
      la = NULL;
    }
  else
    {
      lt2 = t2;
      la = a;
    }
  
  do 
    {
      CUDD->reordered = 0;
      table = cuddHashTableInit (CUDD, 1, 2);
      if (table == NULL) return NULL;
      
      res = tdd_term_replace_recur (tdd, f, t1, lt2, 
				    la, kmin, kmax,table);
      if (res != NULL)
	cuddRef (res);
      cuddHashTableQuit (table);
    } while (CUDD->reordered == 1);
  
  if (res != NULL) cuddDeref (res);
  return (res);
}

/**
 * Constrain f with  t1 <= t2 + k. 
 * f is an LDD, t1 and t2 are terms, k a constant
 */
tdd_node * 
tdd_term_constrain (tdd_manager *tdd, tdd_node *f, linterm_t t1, 
		    linterm_t t2, constant_t k)
{
  tdd_node *res;
  DdHashTable * table;
  
  do 
    {
      CUDD->reordered = 0;
      table = cuddHashTableInit (CUDD, 1, 2);
      if (table == NULL) return NULL;
      
      res = tdd_term_constrain_recur (tdd, f, t1, t2, k,table);
      if (res != NULL)
	cuddRef (res);
      cuddHashTableQuit (table);
    } while (CUDD->reordered == 1);
  
  if (res != NULL) cuddDeref (res);
  return (res);
}


/**
 * Approximates f by computing the min and max bounds for all terms.
 */
tdd_node * 
tdd_term_minmax_approx (tdd_manager *tdd, tdd_node *f)
{
  tdd_node *res;
  
  do 
    {
      CUDD->reordered = 0;
      res = tdd_term_minmax_approx_recur (tdd, f);
    } while (CUDD->reordered == 1);
  return (res);
}



tdd_node *
tdd_box_extrapolate_recur (tdd_manager *tdd,
			   tdd_node *f,
			   tdd_node *g)
{
  DdManager * manager;
  DdNode *F, *fv, *fnv, *G, *gv, *gnv, *Fnv, *Gnv;
  DdNode *one, *zero, *r, *t, *e;
  unsigned int topf, topg, index;

  lincons_t vCons;

  manager = CUDD;
  statLine(manager);
  one = DD_ONE(manager);
  zero = Cudd_Not (one);

  F = Cudd_Regular(f);
  G = Cudd_Regular(g);


  /* Terminal cases. */
  if (F == one || G == one || F == G) return g;

  /* At this point f and g are not constant. */
  /* widen is asymmetric. cannot switch operands */

  /* Check cache. */
  if (F->ref != 1 || G->ref != 1) {
    r = cuddCacheLookup2(manager, (DD_CTFP)tdd_box_extrapolate, f, g);
    if (r != NULL) return(r);
  }
  
  /* Get the levels */
  /* Here we can skip the use of cuddI, because the operands are known
  ** to be non-constant.
  */
  topf = manager->perm[F->index];
  topg = manager->perm[G->index];

  /* Compute cofactors. */
  if (topf <= topg) {
    index = F->index;
    fv = cuddT(F);
    fnv = cuddE(F);
    if (Cudd_IsComplement(f)) {
      fv = Cudd_Not(fv);
      fnv = Cudd_Not(fnv);
    }
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
  vCons = tdd->ddVars [index];

  /** 
   * If f and g have the same term, simplify the THEN part of the
   * non-root diagram. This eliminates a redundant test. This assumes
   * that if a constraint A is less than in diagram ordering than B
   * then A implies B.
   * 
   * We check whether f and g have the same constraint using the
   * following facts: 
   *   vInfo is the constraint of the root diagram
   *   gv == g iff g is not the root diagram
   *   fv == f iff f is not the root diagram
   */
  if (gv == g)
    {
      lincons_t gCons = tdd->ddVars [G->index];
      
      if (THEORY->is_stronger_cons (vCons, gCons))
	{
	  gv = cuddT (G);
	  if (Cudd_IsComplement (g))
	    gv = Cudd_Not (gv);
	}
    }
  else if (fv == f)
    {
      lincons_t fCons = tdd->ddVars [F->index];
      
      if (THEORY->is_stronger_cons (vCons, fCons))
	{
	  fv = cuddT (F);
	  if (Cudd_IsComplement (f))
	    fv = Cudd_Not (fv);
	}
    }
  
  
  
  /* Here, fv, fnv are lhs and rhs of f, 
           gv, gnv are lhs and rhs of g,
	   index is the index of the  root variable 
  */

  t = tdd_box_extrapolate_recur (tdd, fv, gv);
  if (t == NULL) return (NULL);
  cuddRef (t);
  
  e = tdd_box_extrapolate_recur (tdd, fnv, gnv);
  if (e == NULL)
    {
      Cudd_IterDerefBdd (manager, t);
      return NULL;
    }
  cuddRef (e);
  
  r = NULL;

  Fnv = Cudd_Regular (fnv);
  Gnv = Cudd_Regular (gnv);

  if (t == e)
    {
      r = t;
      cuddRef (r);
    }
  /** 
   ** extrapolate to the right
   ** perm[F->index] < perm[G->index]  implies that F and G are different
   ** gv != g  implies that C(f) implies C(g)
   ** perm[G->index] < perm[Fnv->index] implies that C(g) implies C(fnv)
   **/
  else if ( (CUDD->perm[F->index] < CUDD->perm[G->index]) &&
	    (gv != g) &&
	    (Fnv->index == CUDD_CONST_INDEX ||
	     CUDD->perm[G->index] < CUDD->perm[Fnv->index]) &&
	    (fnv == zero || 
	     (Fnv != one &&
	      cuddT (Fnv) == ((fnv == Fnv) ? zero : one))))
    {      
      /* r = OR (t, e) */
      r = tdd_and_recur (tdd, Cudd_Not (t), Cudd_Not (e));
      r = Cudd_NotCond (r, r != NULL);

      if (r == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  Cudd_IterDerefBdd (CUDD, e);
	  return NULL;
	}
      cuddRef (r);

    }
  /** extrapolate to the left */
  else if (CUDD->perm[G->index] < CUDD->perm[F->index] && 
	   fv == zero &&
	   f != fv &&
	   (Gnv->index == CUDD_CONST_INDEX ||
	    CUDD->perm[F->index] < CUDD->perm[Gnv->index]))

    {
      DdNode *h, *k, *w;
      lincons_t fCons;
      
      fnv = cuddE (F);
      fnv = Cudd_NotCond (fnv, F != f);
      Fnv = Cudd_Regular (fnv);
      
      fCons = tdd->ddVars [F->index];
      
      if (Fnv->index != CUDD_CONST_INDEX && 
          THEORY->is_stronger_cons (fCons, tdd->ddVars [Fnv->index]))
	h = Cudd_NotCond (cuddT(Fnv), Fnv != fnv);
      else
	h = fnv;
      
      if (Gnv->index != CUDD_CONST_INDEX && 
          THEORY->is_stronger_cons (vCons, tdd->ddVars [Gnv->index]))
	k = Cudd_NotCond (cuddT (Gnv), Gnv != gnv);
      else
	k = gnv;
      
      /* clear out t and e since we will recompute them */
      Cudd_IterDerefBdd (CUDD, t);
      t = NULL;
      Cudd_IterDerefBdd (CUDD, e);
      e = NULL;
      
      w = tdd_box_extrapolate_recur (tdd, h, k);
      
      if (w == NULL) return NULL;      
      cuddRef (w);

      /* t = OR (gv, w) */
      t = tdd_and_recur (tdd, Cudd_Not (gv), Cudd_Not (w));
      t = Cudd_NotCond (t, t != NULL);

      if (t == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, w);
	  return NULL;
	}
      cuddRef (t);
      Cudd_IterDerefBdd (CUDD, w);
      
      e = tdd_box_extrapolate_recur (tdd, fnv, gnv);
      if (e == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  return NULL;
	}
      cuddRef (e);

    }
  

  if (r == NULL)
    {
      DdNode *root;
      
      root = Cudd_bddIthVar (CUDD, index);

      if (root == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  Cudd_IterDerefBdd (CUDD, e);
	  return NULL;
	}
      cuddRef (root);

      /** XXX should use tdd_unique_inter instead */
      r = tdd_ite_recur (tdd, root, t, e);
      if (r == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  Cudd_IterDerefBdd (CUDD, e);
	  return NULL;
	}
      cuddRef (r);
      Cudd_IterDerefBdd (CUDD, root);
    }
  

  Cudd_IterDerefBdd (CUDD, t);
  Cudd_IterDerefBdd (CUDD, e);

  if (F->ref != 1 || G->ref != 1)
    cuddCacheInsert2(manager, (DD_CTFP)tdd_box_extrapolate, f, g, r);

  cuddDeref (r);
  return r;
  
}

tdd_node * 
tdd_term_replace_recur (tdd_manager * tdd, tdd_node *f, 
			linterm_t t1, linterm_t t2, 
			constant_t a,
			constant_t kmin, constant_t kmax,
			DdHashTable* table)
{
  DdNode *F, *res, *fv, *fnv, *t, *e;
  DdNode *rootT, *rootE;
  
  lincons_t fCons;
  linterm_t fTerm;
  

  F = Cudd_Regular (f);
  
  if (F == DD_ONE (CUDD)) 
    {
      if (t2 == NULL && f == DD_ONE(CUDD))
	{
          /* add   kmin <= t1 <= kmax */

	  lincons_t maxCons;
	  lincons_t minCons;
	  DdNode *tmp1, *tmp2;
	  
	  res = NULL;
	  
	  /* kmax is not +oo */
          if (kmax != NULL)
            {
              maxCons = THEORY->create_cons (THEORY->dup_term (t1), 0,
                                             THEORY->dup_cst (kmax));
              if (maxCons == NULL) 
                  return NULL;
          
              res = to_tdd (tdd, maxCons);
              THEORY->destroy_lincons (maxCons);
              if (res == NULL) return NULL;
              cuddRef (res); 
            }
	  else
	    {
	      /* simplify reference counting */
	      res = DD_ONE(CUDD);
	      cuddRef (res);
	    }
	  
	  /* here, ref count of res is 1 */

	  /* kmin is not -oo */
          if (kmin != NULL)
            {
              minCons = THEORY->create_cons (THEORY->negate_term (t1), 0,
                                             THEORY->negate_cst (kmin));
              if (minCons == NULL) 
                {
                  Cudd_IterDerefBdd (CUDD, res);
                  return NULL;
                }
              tmp1 = to_tdd (tdd, minCons);
              if (tmp1 == NULL)
                {
                  Cudd_IterDerefBdd (CUDD, res);
                  return NULL;
                }
              cuddRef (tmp1);

              tmp2 = tdd_and_recur (tdd, res, tmp1);
              if (tmp2 != NULL) cuddRef (tmp2);
              Cudd_IterDerefBdd (CUDD, res);
              Cudd_IterDerefBdd (CUDD, tmp1);
              if (tmp2 == NULL) return NULL;
              res = tmp2;
            }

	  cuddDeref (res);
	  return res;
	}
      
      return f;  
    }


  /* XXX if terms t1 and t2 do not appear in f, can stop here */

  /* check cache */
  if (F->ref != 1 && ((res = cuddHashTableLookup1 (table, f)) != NULL))
    return res;

  /* cofactors */
  fv = Cudd_NotCond (cuddT(F), F != f);
  fnv = Cudd_NotCond (cuddE(F), F != f);
  

  /* roots of the result diagram */
  rootT = NULL;
  rootE = NULL;
  
  fCons = tdd->ddVars [F->index];
  fTerm = THEORY->get_term (fCons);
  
  /* remove top term if it is t1 */
  if (THEORY->term_equals (fTerm, t1))
    {
      rootT = DD_ONE(CUDD);
      cuddRef (rootT);
      
      rootE = DD_ONE(CUDD);
      cuddRef (rootE);
    }
  /* keep top term if it is not t1 */
  else
    {
      rootT = Cudd_bddIthVar (CUDD, F->index);
      if (rootT == NULL) return NULL;
      cuddRef (rootT);
      
      rootE = Cudd_Not (rootT);
      cuddRef (rootE);
    }
  
  
  /* if top constraint is  t2 < c and a >0 
   *       add t1 < a*c + kmax to the THEN branch
   *      and !(t1 < a*c + kmin) to the ELSE branch 
   *
   * if top constraint is t2 < c and a < 0
   *     add t1 > a*c + kmin to the THEN branch
   *     and t1 < a*c + kmax to the ELSE branch
   */
  if (t2 != NULL && THEORY->term_equals (fTerm, t2))
    {
      DdNode *tmp, *d;
      constant_t fCst, tmpCst, nCst;
      lincons_t newCons;

      int pos; int strict;
      
      pos = THEORY->is_pos_cst (a);
      strict = THEORY->is_strict (fCons);
      fCst = THEORY->get_constant (fCons);

      d = NULL;

      
      /* kmax == NULL means kmax is positive infinity, same for kmin
       * Don't add constraints if the constant is infinity
       */
      if ((pos && kmax != NULL) || (!pos && kmin != NULL))
	{
	  /* nCst = a * fCst + kmax */
	  tmpCst = THEORY->mul_cst (a, fCst);
	  nCst = THEORY->add_cst (tmpCst, pos ? kmax : kmin);
	  THEORY->destroy_cst (tmpCst);
	  tmpCst = NULL;

	  if (!pos) strict = !strict;

	  /* since t2 < fCst, 
	     newCons is  
                 t1 < a * fCst + kmax, if a>0, and
	         t1 <= a * fCst + kmin, if a<0
	   */
	  newCons = THEORY->create_cons (THEORY->dup_term (t1), 
					 strict, 
					 nCst);
	  /* nCst is now managed by createCons */

	  d = to_tdd (tdd, newCons);
	  THEORY->destroy_lincons (newCons);
	  newCons = NULL;
	  if (d == NULL)
	    {
	      Cudd_IterDerefBdd (CUDD, rootT);
	      Cudd_IterDerefBdd (CUDD, rootE);
	      return NULL;
	    }
	  cuddRef (d);

	  /* if a<0, need negation of newCons */
	  d = Cudd_NotCond (d, !pos);

	  /* add d to the THEN branch */
	  tmp = tdd_and_recur (tdd, rootT, d);
	  if (tmp != NULL) cuddRef (tmp);
	  Cudd_IterDerefBdd (CUDD, rootT);
	  if (tmp == NULL)
	    {
	      Cudd_IterDerefBdd (CUDD, rootE);
	      Cudd_IterDerefBdd (CUDD, d);
	      return NULL;
	    }
	  rootT = tmp;
	  tmp = NULL;
	}

      /* have a lower bound */
      if ((pos && kmin != NULL) || (!pos && kmax != NULL))
	{
	  /* if t2 is not NULL then kmin and kmax cannot be both NULL */
	  if (kmin == kmax)
	    /* Same min and max bounds. 
	     * Use negation of the THEN constraint */
	    d = Cudd_Not (d);
	  else /* kmin != kmax */
	    /* compute d for the ELSE branch */
	    {
	      if (d != NULL)
		Cudd_IterDerefBdd (CUDD, d);
	      d = NULL;
	  
	      /* nCst = a * fCst + kmin */
	      tmpCst = THEORY->mul_cst (a, fCst);
	      nCst = THEORY->add_cst (tmpCst, pos ? kmin : kmax);
	      THEORY->destroy_cst (tmpCst);
	      tmpCst = NULL;
      
	      /* since !(t2 <= fCst),
		  newCons is 
		    t1 <=  a*fCst + kmin if a>0, and
                    t1 < a*fCst + kmax if a<0 
		    
		 Note that newCons is used negated if a>0, and as is otherwise
	      */
	      newCons = THEORY->create_cons (THEORY->dup_term (t1), 
					     strict,
					     nCst);
	      /* nCst is now managed by createCons */

	      d = to_tdd (tdd, newCons);
	      THEORY->destroy_lincons (newCons);
	      newCons = NULL;
	      if (d == NULL)
		{
		  Cudd_IterDerefBdd (CUDD, rootT);
		  Cudd_IterDerefBdd (CUDD, rootE);
		  return NULL;
		}
	      cuddRef (d);
	      /* if a>0, need negation of newCons */
	      d = Cudd_NotCond (d, pos);
	    }
      
	  if (d != NULL)
	    {
	      /* add d to the ELSE branch */
	      tmp = tdd_and_recur (tdd, rootE, d);
	      if (tmp != NULL) cuddRef (tmp);
	      Cudd_IterDerefBdd (CUDD, rootE);
	      if (tmp == NULL)
		{
		  Cudd_IterDerefBdd (CUDD, rootT);
		  Cudd_IterDerefBdd (CUDD, d);
		  return NULL;
		}
	      rootE = tmp;
	      Cudd_IterDerefBdd (CUDD, d);
	    }
	}
      
    }
  
      
  /* recursive step */

  t = tdd_term_replace_recur (tdd, fv, t1, t2, a, kmin, kmax, table);
  if (t == NULL)
    {
      Cudd_IterDerefBdd (CUDD, rootT);
      Cudd_IterDerefBdd (CUDD, rootE);
      return NULL;
    }
  cuddRef (t);
  
  e = tdd_term_replace_recur (tdd, fnv, t1, t2, a, kmin, kmax, table);
  if (e == NULL)
    {
      Cudd_IterDerefBdd (CUDD, rootT);
      Cudd_IterDerefBdd (CUDD, rootE);
      Cudd_IterDerefBdd (CUDD, t);
      return NULL;
    }
  cuddRef (e);

  /* Add rootT to the THEN branch of the result */
  if (rootT != DD_ONE(CUDD))
    {
      DdNode *tmp;
      tmp = tdd_and_recur (tdd, rootT, t);
      if (tmp != NULL) cuddRef (tmp);
      Cudd_IterDerefBdd (CUDD, rootT);
      Cudd_IterDerefBdd (CUDD, t);
      if (tmp == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, rootE);
	  Cudd_IterDerefBdd (CUDD, e);
	  return NULL;
	}
      t = tmp; 
    }
  else
    /* rootT == DD_ONE(CUDD) */
    cuddDeref (rootT);
  
  /* Add rootE to the ELSE branch of the result */
  if (rootE != DD_ONE(CUDD))
    {
      DdNode *tmp;
      tmp = tdd_and_recur (tdd, rootE, e);
      if (tmp != NULL) cuddRef (tmp);
      Cudd_IterDerefBdd (CUDD, rootE);
      Cudd_IterDerefBdd (CUDD, e);
      if (tmp == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  return NULL;
	}
      e = tmp; 
    }
  else
    /* rootE == DD_ONE(CUDD) */
    cuddDeref (rootE);


  /* res = OR (t, e) */
  res = tdd_and_recur (tdd, Cudd_Not (t), Cudd_Not (e));
  if (res != NULL)
    {
      res = Cudd_Not (res);
      cuddRef (res);
    }
  Cudd_IterDerefBdd (CUDD, t);
  Cudd_IterDerefBdd (CUDD, e);
  if (res == NULL) return NULL;
  
  /* update cache */
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


tdd_node *
tdd_term_minmax_approx_recur (tdd_manager *tdd,
			      tdd_node *f)
{
  DdManager * manager;
  DdNode *F, *fv, *fnv, *h, *k;
  DdNode *one, *zero, *r, *t;

  unsigned int minIndex, maxIndex;
  lincons_t minCons, maxCons;
  
  manager = CUDD;
  statLine(manager);
  one = DD_ONE(manager);
  zero = Cudd_Not (one);

  F = Cudd_Regular(f);


  /* Terminal cases. */
  if (F == one) return f;


  /* Check cache. */
  if (F->ref != 1) {
    r = cuddCacheLookup1(manager, (DD_CTFP1)tdd_term_minmax_approx, f);
    if (r != NULL) return(r);
  }
  
  minIndex = F->index;

  fv = Cudd_NotCond (cuddT(F), F != f);
  fnv = Cudd_NotCond (cuddE(F), F != f);

  /** 
   * Get the constraint of the root node 
   */
  minCons = tdd->ddVars [minIndex];

  maxCons = minCons;
  maxIndex = minIndex;

  k = fv;
  cuddRef (k);
  
  h = fnv;
  
  while (!cuddIsConstant (Cudd_Regular (h)))
    {
      lincons_t hCons;
      DdNode *H, *tmp, *ht;
      
      H = Cudd_Regular (h);
      hCons = tdd->ddVars [H->index];
      
      if (!THEORY->is_stronger_cons (maxCons, hCons)) break;
      
      maxCons = hCons;
      maxIndex = H->index;
      
      /* THEN branch of h */
      ht = Cudd_NotCond (cuddT(H), H != h);

      /* k = OR (k, ht) */
      tmp = tdd_and_recur (tdd, Cudd_Not (k), Cudd_Not (ht));
      if (tmp != NULL) cuddRef (tmp);
      Cudd_IterDerefBdd (CUDD, k);
      if (tmp == NULL) return NULL;
      k = Cudd_Not (tmp);

      h = Cudd_NotCond (cuddE (H), H != h);
    }
  
  if (h != zero)
    {
      DdNode *tmp;
      
      tmp = tdd_and_recur (tdd, Cudd_Not (k), Cudd_Not (h));
      if (tmp != NULL) cuddRef (tmp);
      Cudd_IterDerefBdd (CUDD, k);
      if (tmp == NULL) return NULL;
      k = Cudd_Not (tmp);
    }
  
  t = tdd_term_minmax_approx_recur (tdd, k);
  if (t != NULL) cuddRef (t);
  Cudd_IterDerefBdd (CUDD, k);
  if (t == NULL) return NULL;
  k = t; t = NULL;
  

  if (h != zero)
    {
      r = k; k = NULL;
    }
  
  else
    {
      DdNode *root;
      
      root = Cudd_bddIthVar (CUDD, maxIndex);
      if (root == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, k);
	  return NULL;
	}
      cuddRef (root);
      
      r = tdd_ite_recur (tdd, root, k, zero);
      if (r != NULL) cuddRef (r);
      Cudd_IterDerefBdd (CUDD, root);
      Cudd_IterDerefBdd (CUDD, k);
      k = NULL;
      if (r == NULL) return NULL;
    }
  
  /* k is dead here, r is referenced once */

  if (fv == zero)
    {
      DdNode *root, *tmp;
      
      root = Cudd_bddIthVar (CUDD, minIndex);
      if (root == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, r);
	  return NULL;
	}
      cuddRef (root);
      
      tmp = tdd_ite_recur (tdd, root, zero, r);
      if (tmp != NULL) cuddRef (tmp);
      Cudd_IterDerefBdd (CUDD, r);
      Cudd_IterDerefBdd (CUDD, root);
      if (tmp == NULL) return NULL;
      r = tmp;
    }
  
  if (F->ref != 1)
    cuddCacheInsert1(CUDD, (DD_CTFP1)tdd_term_minmax_approx, f, r);
  
  cuddDeref (r);
  return r;
}

tdd_node * 
tdd_term_constrain_recur (tdd_manager *tdd, tdd_node *f, linterm_t t1, 
			  linterm_t t2, constant_t k, DdHashTable *table)
{
  DdNode *F, *t, *e, *r;
  lincons_t fCons;
  linterm_t fTerm;
  constant_t fCst;
  DdNode *zero, *tmp;
  
  
  
  F = Cudd_Regular (f);
  zero = Cudd_Not (DD_ONE(CUDD));
  
  if (F == DD_ONE(CUDD)) return f;

  if (F->ref != 1 && (r = cuddHashTableLookup1 (table, f)) != NULL)
    return r;

  fCons = tdd->ddVars [F->index];
  fTerm = THEORY->get_term (fCons);

  t = Cudd_NotCond (cuddT(F), f != F);
  cuddRef (t);
  
  if (t != zero && THEORY->term_equals (fTerm, t2))
    {
      DdNode *d;
      constant_t nCst;
      lincons_t nCons;
      
      /* create  t1 <= fCst + k */
      fCst = THEORY->get_constant (fCons);
      nCst = THEORY->add_cst (fCst, k);
      nCons = THEORY->create_cons (THEORY->dup_term (t1),
				   THEORY->is_strict (fCons),
				   nCst);
      d = to_tdd (tdd, nCons);
      THEORY->destroy_lincons (nCons);
      nCons = NULL;
      if (d == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  return NULL;
	}
      cuddRef (d);
      
      /* add new constraint to t */
      tmp = tdd_and_recur (tdd, t, d);
      if (tmp != NULL) cuddRef (tmp);
      Cudd_IterDerefBdd (CUDD, t);
      Cudd_IterDerefBdd (CUDD, d);
      if (tmp == NULL) return NULL;
      t = tmp;
    }
  
  /* recurse on the THEN branch */
  tmp = tdd_term_constrain_recur (tdd, t, t1, t2, k, table);
  if (tmp != NULL) cuddRef (tmp);
  Cudd_IterDerefBdd (CUDD, t);
  if (tmp == NULL) return NULL;
  t = tmp;
  
  e = Cudd_NotCond (cuddE(F), f != F);
  cuddRef (e);

  if (e != zero && THEORY->term_equals (fTerm, t1))
    {
      DdNode *d;
      constant_t tmpCst, nCst;
      lincons_t nCons;
     
      /* Create  t2 <= fCst - k */
      fCst = THEORY->get_constant (fCons);
      tmpCst = THEORY->negate_cst (k);
      nCst = THEORY->add_cst (tmpCst, fCst);
      THEORY->destroy_cst (tmpCst);
      tmpCst = NULL;
      
      nCons = THEORY->create_cons 
	(THEORY->dup_term (t2), THEORY->is_strict (fCons), nCst);
      d = to_tdd (tdd, nCons);
      THEORY->destroy_lincons (nCons);
      nCons = NULL;
      if (d == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  Cudd_IterDerefBdd (CUDD, e);
	  return NULL;
	}
      cuddRef (d);
      d = Cudd_Not (d);

      /* add new constraint to e */
      tmp = tdd_and_recur (tdd, e, d);
      if (tmp != NULL) cuddRef (tmp);
      Cudd_IterDerefBdd (CUDD, e);
      Cudd_IterDerefBdd (CUDD, d);
      if (tmp == NULL) 
	{
	  Cudd_IterDerefBdd (CUDD, t);
	  return NULL;
	}
      e = tmp;
      
    }

  /* recurse on the ELSE branch */
  tmp = tdd_term_constrain_recur (tdd, e, t1, t2, k, table);
  if (tmp != NULL) cuddRef (tmp);
  Cudd_IterDerefBdd (CUDD, e);
  if (tmp == NULL)
    {
      Cudd_IterDerefBdd (CUDD, t);
      return NULL;
    }
  e = tmp;
  
  
  /* construct the result */
  r = tdd_ite_recur (tdd, CUDD->vars[F->index], t, e);

  
  if (r != NULL) cuddRef (r);
  Cudd_IterDerefBdd (CUDD, t);
  Cudd_IterDerefBdd (CUDD, e);
  if (r == NULL) return NULL;

  if (F->ref != 1)
    {
      ptrint fanout = (ptrint) F->ref;
      cuddSatDec (fanout);
      if (!cuddHashTableInsert1 (table, f, r, fanout));
      {
	Cudd_IterDerefBdd (CUDD, r);
	return NULL;
      }
    }

  cuddDeref (r);
  return r;
  
}



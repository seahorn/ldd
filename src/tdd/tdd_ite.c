#include "util.h"
#include "theory.h"


static int bddVarToCanonicalSimple (DdManager *dd, DdNode **fp, DdNode **gp, DdNode **hp, unsigned int *topfp, unsigned int *topgp, unsigned int *tophp);



tdd_node * tdd_ite (tdd_manager *tdd, tdd_node *f, tdd_node *g, tdd_node *h)
{
  tdd_node *res;
  
  do {
    CUDD->reordered = 0;
    res = tdd_ite_recur (tdd, f, g, h);
  } while (CUDD->reordered == 1);
  
  return (res);
}


tdd_node * tdd_and (tdd_manager *tdd, tdd_node * f, tdd_node *g)
{
  tdd_node *res;
  
  do {
    CUDD->reordered = 0;
    res = tdd_and_recur (tdd, f, g);
  } while (CUDD->reordered == 1);
  return (res);
}



tdd_node * dddOr (tdd_manager* tdd,
		  tdd_node * f,
		  tdd_node * g)
{
  tdd_node * res;
  
  do {
    CUDD->reordered = 0;
    res = tdd_and_recur (tdd, Cudd_Not (f), Cudd_Not (g));
  } while (CUDD->reordered == 1);
  
  res = Cudd_NotCond (res, res != NULL);
  return (res);
}

tdd_node * tdd_xor (tdd_manager * tdd,
		    tdd_node * f,
		    tdd_node *g)
{
  tdd_node *res;
  
  do {
    CUDD->reordered = 0;
    res = tdd_xor_recur (tdd, f, g);
  } while (CUDD->reordered == 1);
  return (res);
}




/**
 * Required: 
 *    f != g
 */
tdd_node* tdd_unique_inter (tdd_manager *tdd, unsigned int index, 
			    tdd_node *f, tdd_node *g)
{
  tdd_node * res;
  DdNode  *v, *t, *e;

  DdNode *F;
  DdNode *G;
  DdNode *V;
  



  v = Cudd_bddIthVar (CUDD, index);
  if (v == NULL) return NULL;

  F = Cudd_Regular (f);
  G = Cudd_Regular (g);
  /* both f and g are constants */
  if (F == G)
    return Cudd_NotCond (v, g == DD_ONE(CUDD));

  /* from this point on, we will need v */
  cuddRef (v);
  V = Cudd_Regular (v);

  /* Using: (!v -> f, g) === (v -> g, f) */
  if (!Cudd_IsComplement (v))
    {
      t = f;
      e = g;
    }
  else
    {
      t = g;
      e = f;
    }
  


  /*** 
   *** TDD Simplification
   ***  (v -> t, (e->x, y)) == e if  v is_stronger_cons than e and t == x     
   ***                          
   ***/
  if (!Cudd_IsConstant (e))
    {
      lincons_t vCons = tdd->ddVars [V->index];
      lincons_t eCons = tdd->ddVars [Cudd_Regular (e)->index];

      if (THEORY->is_stronger_cons (vCons, eCons))
	{
	  DdNode * x;
	  DdNode * E;
	  
	  /* take THEN cofactor of e */
	  E = Cudd_Regular (e);
	  x = Cudd_NotCond (cuddE (E), e != E);

	  if (t == x) 
	    {
	      Cudd_IterDerefBdd (CUDD, v);
	      return e;
	    }
	}
    }
  

  /* Ensure that then branch is not complemented */
  if (Cudd_IsComplement (t))
    {
      /* Using: (v -> t, e) === !(v -> !t, !e)  */
      res = 
	cuddUniqueInter (CUDD, (int)index, Cudd_Not (t), Cudd_Not (e));
      if (res == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, v);
	  return NULL;
	}
      res = Cudd_Not (res);
    }
  else
    {
      res = cuddUniqueInter (CUDD, (int)index, t, e);
      if (res == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, v);
	  return NULL;
	}
    }
  
  Cudd_IterDerefBdd (CUDD, v);
  return res;
}




tdd_node * tdd_ite_recur (tdd_manager * tdd,
			  tdd_node *f,
			  tdd_node *g,
			  tdd_node *h)
{
  DdNode	 *one, *zero, *res;
  DdNode	 *r, *Fv, *Fnv, *Gv, *Gnv, *H, *Hv, *Hnv, *t, *e;
  unsigned int topf, topg, toph, v;
  int		 index;
  int		 comple;
  DdManager *dd;
  
  lincons_t vCons;
  
  statLine(CUDD);
  /* Terminal cases. */

  /* One variable cases. */
  if (f == (one = DD_ONE(CUDD))) 	/* ITE(1,G,H) = G */
    return(g);
    
  if (f == (zero = Cudd_Not(one))) 	/* ITE(0,G,H) = H */
    return(h);

  /* From now on, f is known not to be a constant. */
  if (g == one || f == g) {	/* ITE(F,F,H) = ITE(F,1,H) = F + H */
    if (h == zero) {	/* ITE(F,1,0) = F */
      return(f);
    } else {
      res = tdd_and_recur(tdd,Cudd_Not(f),Cudd_Not(h));
      return(Cudd_NotCond(res,res != NULL));
    }
  } else if (g == zero || f == Cudd_Not(g)) { 
    /* ITE(F,!F,H) = ITE(F,0,H) = !F * H */
    if (h == one) {		/* ITE(F,0,1) = !F */
      return(Cudd_Not(f));
    } else {
      res = tdd_and_recur(tdd,Cudd_Not(f),h);
      return(res);
    }
  }
  if (h == zero || f == h) {    /* ITE(F,G,F) = ITE(F,G,0) = F * G */
    res = tdd_and_recur(tdd,f,g);
    return(res);
  } else if (h == one || f == Cudd_Not(h)) { 
    /* ITE(F,G,!F) = ITE(F,G,1) = !F + G */
    res = tdd_and_recur(tdd,f,Cudd_Not(g));
    return(Cudd_NotCond(res,res != NULL));
  }

  /* Check remaining one variable case. */
  if (g == h) { 		/* ITE(F,G,G) = G */
    return(g);
  } else if (g == Cudd_Not(h)) { /* ITE(F,G,!G) = F <-> G */
    res = tdd_xor_recur(tdd,f,h);
    return(res);
  }

  /* From here, there are no constants. */
  comple = bddVarToCanonicalSimple(CUDD, &f, &g, &h, &topf, &topg, &toph);

  /* f & g are now regular pointers */
  
  /* v is the minimal level between g and h */
  v = ddMin(topg, toph);

  /* A shortcut: ITE(F,G,H) = (v,G,H) if F = (v,1,0), v < top(G,H). */
  if (topf < v && cuddT(f) == one && cuddE(f) == zero) {
    r = tdd_unique_inter (tdd, f->index, g, h);
    return(Cudd_NotCond(r,comple && r != NULL));
  }

  /* Check cache. */
  r = cuddCacheLookup(dd, DD_TDD_ITE_TAG, f, g, h);
  if (r != NULL) {
    return(Cudd_NotCond(r,comple));
  }


  /* Compute cofactors. */
  if (topf <= v) {
    v = ddMin(topf, v);	/* v = top_var(F,G,H) */
    index = f->index;
    Fv = cuddT(f); Fnv = cuddE(f);
  } else {
    Fv = Fnv = f;
  }
  if (topg == v) {
    index = g->index;
    Gv = cuddT(g); Gnv = cuddE(g);
  } else {
    Gv = Gnv = g;
  }
  if (toph == v) {
    H = Cudd_Regular(h);
    index = H->index;
    Hv = cuddT(H); Hnv = cuddE(H);
    if (Cudd_IsComplement(h)) {
      Hv = Cudd_Not(Hv);
      Hnv = Cudd_Not(Hnv);
    }
  } else {
    Hv = Hnv = h;
  }

  vCons = tdd->ddVars [index];

  /** Propagate implication of the top node */
  if (Fv == f)
    {
      lincons_t fCons = tdd->ddVars [f->index];
      
      if (THEORY->is_stronger_cons (vCons, fCons))
	Fv = cuddT (Fv);
    }
  if (Gv == g)
    {
      lincons_t gCons = tdd->ddVars [g->index];
      if (THEORY->is_stronger_cons (vCons, gCons))
	Gv = cuddT (Gv);
    }
  if (Hv == h)
    {
      H = Cudd_Regular (h);
      lincons_t hCons = tdd->ddVars [H->index];
      if (THEORY->is_stronger_cons (vCons, hCons))
	{
	  Hv = cuddT (H);
	  if (Cudd_IsComplement (h))
	    Hv = Cudd_Not (Hv);
	}
    }
  
  

  /* Recursive step. */
  t = tdd_ite_recur(tdd,Fv,Gv,Hv);
  if (t == NULL) return(NULL);
  cuddRef(t);

  e = tdd_ite_recur(tdd,Fnv,Gnv,Hnv);
  if (e == NULL) {
    Cudd_IterDerefBdd(CUDD,t);
    return(NULL);
  }
  cuddRef(e);

  r = (t == e) ? t : tdd_unique_inter(tdd, index, t, e);
  if (r == NULL) {
    Cudd_IterDerefBdd(CUDD,t);
    Cudd_IterDerefBdd(CUDD,e);
    return(NULL);
  }
  cuddDeref(t);
  cuddDeref(e);

  cuddCacheInsert(CUDD, DD_TDD_ITE_TAG, f, g, h, r);
  return(Cudd_NotCond(r,comple));
}




tdd_node * tdd_and_recur (tdd_manager * tdd,
			  tdd_node *f,
			  tdd_node *g)
{
  DdManager * manager;
  DdNode *F, *fv, *fnv, *G, *gv, *gnv;
  DdNode *one, *r, *t, *e;
  unsigned int topf, topg, index;

  lincons_t vCons;

  manager = CUDD;
  statLine(manager);
  one = DD_ONE(manager);

  /* Terminal cases. */
  F = Cudd_Regular(f);
  G = Cudd_Regular(g);
  if (F == G) {
    if (f == g) return(f);
    else return(Cudd_Not(one));
  }
  if (F == one) {
    if (f == one) return(g);
    else return(f);
  }
  if (G == one) {
    if (g == one) return(f);
    else return(g);
  }

  /* At this point f and g are not constant. */
  if (f > g) { /* Try to increase cache efficiency. */
    DdNode *tmp = f;
    f = g;
    g = tmp;
    F = Cudd_Regular(f);
    G = Cudd_Regular(g);
  }

  /* Check cache. */
  if (F->ref != 1 || G->ref != 1) {
    r = cuddCacheLookup2(manager, (DD_CTFP)tdd_and, f, g);
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
	   index is the index of the new root variable 
  */

  t = tdd_and_recur (tdd, fv, gv);
  if (t == NULL) return(NULL);
  cuddRef(t);
  
  e = tdd_and_recur(tdd, fnv, gnv);
  if (e == NULL) {
    Cudd_IterDerefBdd(manager, t);
	return(NULL);
  }
  cuddRef(e);

  if (t == e) {
    r = t;
  } else {
    if (Cudd_IsComplement(t)) {
      /* push the negation up from t to r */
      r = tdd_unique_inter(tdd, index,
			   Cudd_Not(t),Cudd_Not(e));
      if (r == NULL) {
	Cudd_IterDerefBdd(manager, t);
	Cudd_IterDerefBdd(manager, e);
	return(NULL);
      }
      r = Cudd_Not(r);
    } else {
      r = tdd_unique_inter(tdd,index, t, e);
      if (r == NULL) {
	Cudd_IterDerefBdd(manager, t);
	Cudd_IterDerefBdd(manager, e);
	return(NULL);
      }
    }
  }
  cuddDeref(e);
  cuddDeref(t);
  if (F->ref != 1 || G->ref != 1)
    cuddCacheInsert2(manager, (DD_CTFP)tdd_and, f, g, r);
  return(r);
}


tdd_node * tdd_xor_recur (tdd_manager * tdd,
			  tdd_node *f,
			  tdd_node *g)
{
  DdManager * manager;
  DdNode *F, *fv, *fnv, *G, *gv, *gnv;
  DdNode *one, *zero, *r, *t, *e;
  unsigned int topf, topg, index;
  
  lincons_t vCons;



  manager = CUDD;
  statLine(manager);
  one = DD_ONE(manager);
  zero = Cudd_Not(one);

    /* Terminal cases. */
  if (f == g) return(zero);
  if (f == Cudd_Not(g)) return(one);
  if (f > g) { /* Try to increase cache efficiency and simplify tests. */
    DdNode *tmp = f;
    f = g;
    g = tmp;
  }
  if (g == zero) return(f);
  if (g == one) return(Cudd_Not(f));
  if (Cudd_IsComplement(f)) {
    f = Cudd_Not(f);
    g = Cudd_Not(g);
  }
  /* Now the first argument is regular. */
  if (f == one) return(Cudd_Not(g));
  
  /* At this point f and g are not constant. */
  
  /* Check cache. */
  r = cuddCacheLookup2(manager, (DD_CTFP)tdd_xor, f, g);
  if (r != NULL) return(r);


  /* Get the levels */
  /* Here we can skip the use of cuddI, because the operands are known
  ** to be non-constant.
  */
  topf = manager->perm[f->index];
  G = Cudd_Regular (g);
  topg = manager->perm[G->index];

  
  /* Compute cofactors. */
  if (topf <= topg) {
    index = f->index;
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
  vCons = tdd->ddVars [index];

  /** 
   * If f and g have the same constraint, simplify the THEN part
   * of the non-root diagram.
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
      lincons_t fCons;
      
      fCons = tdd->ddVars[f->index];
      if (THEORY->is_stronger_cons (vCons, fCons))
	{
	  fv = cuddT (f);
	}
    }
  
  
  
  /* Here, fv, fnv are lhs and rhs of f, 
           gv, gnv are lhs and rhs of g,
	   index is the index of the new root variable 
  */

  t = tdd_xor_recur(tdd, fv, gv);
  if (t == NULL) return(NULL);
  cuddRef(t);
  
  e = tdd_xor_recur(tdd, fnv, gnv);
  if (e == NULL) {
    Cudd_IterDerefBdd(manager, t);
	return(NULL);
  }
  cuddRef(e);

  if (t == e) {
    r = t;
  } else {
    if (Cudd_IsComplement(t)) {
      /* push the negation up from t to r */
      r = tdd_unique_inter(tdd, index,
			   Cudd_Not(t),Cudd_Not(e));
      if (r == NULL) {
	Cudd_IterDerefBdd(manager, t);
	Cudd_IterDerefBdd(manager, e);
	return(NULL);
      }
      r = Cudd_Not(r);
    } else {
      r = tdd_unique_inter(tdd,index, t, e);
      if (r == NULL) {
	Cudd_IterDerefBdd(manager, t);
	Cudd_IterDerefBdd(manager, e);
	return(NULL);
      }
    }
  }
  cuddDeref(e);
  cuddDeref(t);
  if (F->ref != 1 || G->ref != 1)
    cuddCacheInsert2(manager, (DD_CTFP)tdd_xor, f, g, r);
  return(r);
}




/* This function is taken from cudd */

/**Function********************************************************************

  Synopsis [Picks unique member from equiv expressions.]

  Description [Makes sure the first two pointers are regular.  This
  may require the complementation of the result, which is signaled by
  returning 1 instead of 0.  This function is simpler than the general
  case because it assumes that no two arguments are the same or
  complementary, and no argument is constant.]

  SideEffects [None]

  SeeAlso     [bddVarToConst bddVarToCanonical]

******************************************************************************/
static int
bddVarToCanonicalSimple(
  DdManager * dd,
  DdNode ** fp,
  DdNode ** gp,
  DdNode ** hp,
  unsigned int * topfp,
  unsigned int * topgp,
  unsigned int * tophp)
{
    register DdNode		*r, *f, *g, *h;
    int				comple, change;

    f = *fp;
    g = *gp;
    h = *hp;

    change = 0;

    /* adjust pointers so that the first 2 arguments to ITE are regular */
    if (Cudd_IsComplement(f)) {	/* ITE(!F,G,H) = ITE(F,H,G) */
	f = Cudd_Not(f);
	r = g;
	g = h;
	h = r;
	change = 1;
    }
    comple = 0;
    if (Cudd_IsComplement(g)) {	/* ITE(F,!G,H) = !ITE(F,G,!H) */
	g = Cudd_Not(g);
	h = Cudd_Not(h);
	change = 1;
	comple = 1;
    }
    if (change) {
	*fp = f;
	*gp = g;
	*hp = h;
    }

    /* Here we can skip the use of cuddI, because the operands are known
    ** to be non-constant.
    */
    *topfp = dd->perm[f->index];
    *topgp = dd->perm[g->index];
    *tophp = dd->perm[Cudd_Regular(h)->index];

    return(comple);

} /* end of bddVarToCanonicalSimple */


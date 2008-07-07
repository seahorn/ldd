#include "util.h"
#include "dddCuddInt.h"


DdNode * dddAndRecur (dddManager*, DdNode*, DdNode*);
DdNode * dddXorRecur (dddManager*, DdNode*, DdNode*);
DdNode * dddIteRecur (dddManager*, DdNode*, DdNode*, DdNode*);


static int bddVarToCanonicalSimple (DdManager *dd, DdNode **fp, DdNode **gp, DdNode **hp, unsigned int *topfp, unsigned int *topgp, unsigned int *tophp);



DdNode *
dddIte (dddManager * ddd,
	DdNode *f,
	DdNode *g,
	DdNode *h)
{
  DdNode *res;
  
  do {
    ddd->cudd->reordered = 0;
    res = dddIteRecur (ddd, f, g, h);
  } while (ddd->cudd->reordered == 1);
  
  return (res);
}


DdNode * 
dddAnd (dddManager * ddd,
	DdNode * f,
	DdNode *g)
{
  DdNode *res;
  
  do {
    ddd->cudd->reordered = 0;
    res = dddAndRecur (ddd, f, g);
  } while (ddd->cudd->reordered == 1);
  return (res);
}



DdNode * 
dddOr (dddManager * ddd,
       DdNode * f,
       DdNode * g)
{
  DdNode * res;
  
  do {
    ddd->cudd->reordered = 0;
    res = dddAndRecur (ddd, Cudd_Not (f), Cudd_Not (g));
  } while (ddd->cudd->reordered == 1);
  
  res = Cudd_NotCond (res, res != NULL);
  return (res);
}

DdNode * 
dddXor (dddManager * ddd,
	DdNode * f,
	DdNode *g)
{
  DdNode *res;
  
  do {
    ddd->cudd->reordered = 0;
    res = dddXorRecur (ddd, f, g);
  } while (ddd->cudd->reordered == 1);
  return (res);
}


/*--------------------------------------------------------------------------*/
/* Definition of internal functions                                         */
/*--------------------------------------------------------------------------*/


DdNode *
dddAndRecur (dddManager * ddd,
	     DdNode *f,
	     DdNode *g)
{
  DdManager * manager;
  DdNode *F, *fv, *fnv, *G, *gv, *gnv;
  DdNode *one, *r, *t, *e;
  unsigned int topf, topg, index;
  pvinfo vInfo;


  manager = ddd->cudd;
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
    r = cuddCacheLookup2(manager, (DD_CTFP)dddAnd, f, g);
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
  vInfo = DDD_VAR_INFO (ddd, index);

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
      pvinfo gInfo;
      gInfo = DDD_VAR_INFO (ddd, G->index);
      
      if (DDD_SAME_DIM (vInfo, gInfo))
	{
	  gv = cuddT (G);
	  if (Cudd_IsComplement (g))
	    gv = Cudd_Not (gv);
	}
    }
  else if (fv == f)
    {
      pvinfo fInfo;
      fInfo = DDD_VAR_INFO (ddd, F->index);
      
      if (DDD_SAME_DIM (vInfo, fInfo))
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

  t = dddAndRecur(ddd, fv, gv);
  if (t == NULL) return(NULL);
  cuddRef(t);
  
  e = dddAndRecur(ddd, fnv, gnv);
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
      r = dddUniqueInter(ddd, vInfo->fst, vInfo->snd, vInfo->cst,
			 Cudd_Not(t),Cudd_Not(e));
      if (r == NULL) {
	Cudd_IterDerefBdd(manager, t);
	Cudd_IterDerefBdd(manager, e);
	return(NULL);
      }
      r = Cudd_Not(r);
    } else {
      r = dddUniqueInter(ddd,vInfo->fst, vInfo->snd, vInfo->cst, t, e);
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
    cuddCacheInsert2(manager, (DD_CTFP)dddAnd, f, g, r);
  return(r);
}


DdNode *
dddXorRecur (dddManager * ddd,
	     DdNode *f,
	     DdNode *g)
{
  DdManager * manager;
  DdNode *F, *fv, *fnv, *G, *gv, *gnv;
  DdNode *one, *zero, *r, *t, *e;
  unsigned int topf, topg, index;
  pvinfo vInfo;


  manager = ddd->cudd;
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
  r = cuddCacheLookup2(manager, (DD_CTFP)dddXor, f, g);
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
  vInfo = DDD_VAR_INFO (ddd, index);

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
      pvinfo gInfo;
      gInfo = DDD_VAR_INFO (ddd, G->index);
      
      if (DDD_SAME_DIM (vInfo, gInfo))
	{
	  gv = cuddT (G);
	  if (Cudd_IsComplement (g))
	    gv = Cudd_Not (gv);
	}
    }
  else if (fv == f)
    {
      pvinfo fInfo;
      fInfo = DDD_VAR_INFO (ddd, f->index);
      
      if (DDD_SAME_DIM (vInfo, fInfo))
	{
	  fv = cuddT (f);
	}
    }
  
  
  
  /* Here, fv, fnv are lhs and rhs of f, 
           gv, gnv are lhs and rhs of g,
	   index is the index of the new root variable 
  */

  t = dddXorRecur(ddd, fv, gv);
  if (t == NULL) return(NULL);
  cuddRef(t);
  
  e = dddXorRecur(ddd, fnv, gnv);
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
      r = dddUniqueInter(ddd, vInfo->fst, vInfo->snd, vInfo->cst,
			 Cudd_Not(t),Cudd_Not(e));
      if (r == NULL) {
	Cudd_IterDerefBdd(manager, t);
	Cudd_IterDerefBdd(manager, e);
	return(NULL);
      }
      r = Cudd_Not(r);
    } else {
      r = dddUniqueInter(ddd,vInfo->fst, vInfo->snd, vInfo->cst, t, e);
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
    cuddCacheInsert2(manager, (DD_CTFP)dddXor, f, g, r);
  return(r);
}





DdNode *
dddIteRecur (dddManager * ddd,
	     DdNode *f,
	     DdNode *g,
	     DdNode *h)
{
  DdNode	 *one, *zero, *res;
  DdNode	 *r, *Fv, *Fnv, *Gv, *Gnv, *H, *Hv, *Hnv, *t, *e;
  unsigned int topf, topg, toph, v;
  int		 index;
  int		 comple;
  DdManager *dd;
  pvinfo vInfo;
  
  dd = ddd->cudd;
  
  statLine(dd);
  /* Terminal cases. */

  /* One variable cases. */
  if (f == (one = DD_ONE(dd))) 	/* ITE(1,G,H) = G */
    return(g);
    
  if (f == (zero = Cudd_Not(one))) 	/* ITE(0,G,H) = H */
    return(h);

  /* From now on, f is known not to be a constant. */
  if (g == one || f == g) {	/* ITE(F,F,H) = ITE(F,1,H) = F + H */
    if (h == zero) {	/* ITE(F,1,0) = F */
      return(f);
    } else {
      res = dddAndRecur(ddd,Cudd_Not(f),Cudd_Not(h));
      return(Cudd_NotCond(res,res != NULL));
    }
  } else if (g == zero || f == Cudd_Not(g)) { 
    /* ITE(F,!F,H) = ITE(F,0,H) = !F * H */
    if (h == one) {		/* ITE(F,0,1) = !F */
      return(Cudd_Not(f));
    } else {
      res = dddAndRecur(ddd,Cudd_Not(f),h);
      return(res);
    }
  }
  if (h == zero || f == h) {    /* ITE(F,G,F) = ITE(F,G,0) = F * G */
    res = dddAndRecur(ddd,f,g);
    return(res);
  } else if (h == one || f == Cudd_Not(h)) { 
    /* ITE(F,G,!F) = ITE(F,G,1) = !F + G */
    res = dddAndRecur(ddd,f,Cudd_Not(g));
    return(Cudd_NotCond(res,res != NULL));
  }

  /* Check remaining one variable case. */
  if (g == h) { 		/* ITE(F,G,G) = G */
    return(g);
  } else if (g == Cudd_Not(h)) { /* ITE(F,G,!G) = F <-> G */
    res = dddXorRecur(ddd,f,h);
    return(res);
  }

  /* From here, there are no constants. */
  comple = bddVarToCanonicalSimple(dd, &f, &g, &h, &topf, &topg, &toph);

  /* f & g are now regular pointers */
  
  /* v is the minimal level between g and h */
  v = ddMin(topg, toph);

  /* A shortcut: ITE(F,G,H) = (v,G,H) if F = (v,1,0), v < top(G,H). */
  if (topf < v && cuddT(f) == one && cuddE(f) == zero) {
    pvinfo fInfo = DDD_VAR_INFO (ddd, f->index);
    r = dddUniqueInter (ddd, fInfo->fst, fInfo->snd, fInfo->cst, g, h);
    return(Cudd_NotCond(r,comple && r != NULL));
  }

  /* Check cache. */
  r = cuddCacheLookup(dd, DD_DDD_ITE_TAG, f, g, h);
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

  vInfo = DDD_VAR_INFO (ddd, index);

  /** Propagate implication of the top node */
  if (Fv == f)
    {
      pvinfo fInfo = DDD_VAR_INFO (ddd, f->index);

      if (DDD_SAME_DIM (vInfo, fInfo))
	Fv = cuddT (Fv);
    }
  if (Gv == g)
    {
      pvinfo gInfo = DDD_VAR_INFO (ddd, g->index);
      if (DDD_SAME_DIM (vInfo, gInfo))
	Gv = cuddT (Gv);
    }
  if (Hv == h)
    {
      H = Cudd_Regular (h);
      pvinfo hInfo = DDD_VAR_INFO (ddd, H->index);
      if (DDD_SAME_DIM (vInfo, hInfo))
	{
	  Hv = cuddT (H);
	  if (Cudd_IsComplement (h))
	    Hv = Cudd_Not (Hv);
	}
    }
  
  

  /* Recursive step. */
  t = dddIteRecur(ddd,Fv,Gv,Hv);
  if (t == NULL) return(NULL);
  cuddRef(t);

  e = dddIteRecur(ddd,Fnv,Gnv,Hnv);
  if (e == NULL) {
    Cudd_IterDerefBdd(dd,t);
    return(NULL);
  }
  cuddRef(e);

  r = (t == e) ? t : dddUniqueInter(ddd,
				    vInfo->fst,
				    vInfo->snd,
				    vInfo->cst, t, e);
    if (r == NULL) {
    Cudd_IterDerefBdd(dd,t);
    Cudd_IterDerefBdd(dd,e);
    return(NULL);
  }
  cuddDeref(t);
  cuddDeref(e);

  cuddCacheInsert(dd, DD_DDD_ITE_TAG, f, g, h, r);
  return(Cudd_NotCond(r,comple));
}


/**
 * Required: 
 *    f != g
 */
DdNode * 
dddUniqueInter (dddManager *ddd, 
		int fst, int snd, int cst, 
		DdNode *f, DdNode *g)
{
  DdNode * res;
  DdNode *v, *t, *e;

  DdNode *F;
  DdNode *G;
  DdNode *V;
  
  unsigned int index;
  
  
  /* create DdNode for the root constraint */
  v = dddCons (ddd, fst, snd, cst);
  if (v == NULL || cuddIsConstant (v)) return v;

  F = Cudd_Regular (f);
  G = Cudd_Regular (g);
  /* both f and g are constants */
  if (F == G)
    return Cudd_NotCond (v, g == DD_ONE(ddd->cudd));

  /* from this point on, we will need v */
  cuddRef (v);
  V = Cudd_Regular (v);
  index = V->index;

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
   *** DDD Simplification
   ***  (v -> t, (e->x, y)) == e      if vars(v) == vars(e) && t == x
   ***/
  if (!Cudd_IsConstant (e))
    {
      pvinfo vInfo, eInfo;  

      vInfo = DDD_VAR_INFO(ddd, V->index);
      eInfo = DDD_VAR_INFO(ddd, Cudd_Regular (e)->index);

      if (DDD_SAME_DIM (vInfo, eInfo))
	{
	  DdNode * x;
	  DdNode * E;
	  
	  assert (vInfo->cst < eInfo->cst);
	  
	  /* take THEN cofactor of e */
	  E = Cudd_Regular (e);
	  x = Cudd_NotCond (cuddE (E), e != E);

	  if (t == x) 
	    {
	      Cudd_IterDerefBdd (ddd->cudd, v);
	      return e;
	    }
	}
    }
  

  /* Ensure that then branch is not complemented */
  if (Cudd_IsComplement (t))
    {
      /* Using: (v -> t, e) === !(v -> !t, !e)  */
      res = 
	cuddUniqueInter (ddd->cudd, (int)index, Cudd_Not (t), Cudd_Not (e));
      if (res == NULL)
	{
	  Cudd_IterDerefBdd (ddd->cudd, v);
	  return NULL;
	}
      res = Cudd_Not (res);
    }
  else
    {
      res = cuddUniqueInter (ddd->cudd, (int)index, t, e);
      if (res == NULL)
	{
	  Cudd_IterDerefBdd (ddd->cudd, v);
	  return NULL;
	}
    }
  
  Cudd_IterDerefBdd (ddd->cudd, v);
  return res;
}


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


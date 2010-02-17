#include <stdio.h>

#include "util.h"
#include "tddInt.h"

static void ddClearFlag(LddNode * n);
static void ddOccurCount (LddManager *ldd, LddNode *N, int *occurrences);


void 
Ldd_ManagerDebugDump (LddManager* ldd)
{
  int i;
  
  fprintf (stderr, "LddManager @%p\n", ldd);
  fprintf (stderr, "\tcudd @%p, theory @%p\n", ldd->cudd, ldd->theory);
  fprintf (stderr, "\tvarsSize=%d\n", ldd->varsSize);

  for (i = 0; i < ldd->varsSize; i++)
    {
      fprintf (stderr, "\t %d: %d: ", i, CUDD->perm[i]);
      if (ldd->ddVars [i] == NULL)
	fprintf (stderr, "(nil)");
      else
	ldd->theory->print_lincons (stderr, ldd->ddVars [i]);

      fprintf (stderr, "\n");
    }
}



/**
 * Computes the number of paths in a diagram.  Running time is linear
 * in the number of path, exponential in the size of the diagram.
 *
 * ldd argument is deprecated. 
 */
int 
Ldd_PathSize (LddManager * ldd, LddNode * n)
{
  LddNode * N, *t, *e;
  
  /* LddNode *one, *zero; */
  
  if (n == NULL) return 0;

  /* one = Ldd_GetTrue (ldd); */
  /* zero = Ldd_Not (one); */
  
  /* if (n == one) return 1; */
  /* if (n == zero) return 0; */

  N = Cudd_Regular (n);
  
  // -- n is TRUE if it is a non-negated constant
  // -- n is FALSE if it is a negated constant
  if (cuddIsConstant (N))
    return n == N ? 1 : 0;

  t = Cudd_NotCond (cuddT (N), n != N);
  e = Cudd_NotCond (cuddE (N), n != N);

  return Ldd_PathSize (ldd, t) + Ldd_PathSize (ldd, e);  
}


/** Checks sanity of the datastructures. Aborts execution on error */
void 
Ldd_SanityCheck (LddManager * ldd)
{
  unsigned int i, j;
  DdSubtable *subtable;
  DdNodePtr *nodelist;
  DdNode *node;
  DdNode *sentinel = &(CUDD->sentinel);

  for (i = 0; i < CUDD->size; i++)
    {
      /* skip empty subtables */
      if (CUDD->subtables [i].keys == 0) continue;

      subtable = &(CUDD->subtables [i]);
      nodelist = subtable->nodelist;
      
      for (j = 0; j < subtable->slots; j++)
	for (node = nodelist [j]; node != sentinel; node = node->next)
	    Ldd_NodeSanityCheck (ldd, (LddNode*)node);
    }
}

void
Ldd_NodeSanityCheck (LddManager *ldd, LddNode *n)
{
  DdNode *f, *g, *G;
  
  lincons_t *nCons, *fCons, *gCons;

  assert (n == Cudd_Regular (n));
  
  f = cuddT (n);
  g = cuddE (n);
  G = Cudd_Regular (g);


  /* basic DD ordering */
  assert (cuddI (CUDD, n->index) < cuddI(CUDD, f->index));
  assert (cuddI (CUDD, n->index) < cuddI(CUDD,  G->index));

  nCons = ldd->ddVars [n->index];
  

  /* THEN edge is not negated */
  assert (f == Cudd_Regular (f));

  if (f != DD_ONE(CUDD))
    {
      fCons = ldd->ddVars [f->index];
      
      /* redundant decision */
      assert (!THEORY->is_stronger_cons (nCons, fCons));
    }
  
  if (G != DD_ONE(CUDD))
    {
      DdNode *g1;
      
      gCons = ldd->ddVars [G->index];
      
      g1 = Cudd_NotCond (cuddT (G), g != G);

      /* for a decomposition of the form
	 ITE (n, f, ITE (g, g1, g0))
	 either NOT cons(n) stronger than cons(g) or f != g0
      */
      assert (g1 != f || !THEORY->is_stronger_cons (nCons, gCons));
    }
  
  

}


/**
 * \brief Returns the number of times each variable occurs in an LDD.
  
  \param ldd manager
  \param n LDD node

  \param[out] occurrences the number of occurrences of variable i is
  the ith element of the array

  \pre The size of the occurrences array is at least the number of
  variables in n.
 */
void
Ldd_SupportVarOccurrences (LddManager *ldd, 
			   LddNode *n, 
			   int* occurrences)
{

  int *support;
  size_t size, i;
  
  lincons_t vCons;
  linterm_t vTerm, pTerm;


  /* no variables in the constant node */
  if (Cudd_IsConstant (n)) return;

  /* compute the support. */
  size = CUDD->size;
  support = Cudd_SupportIndex (CUDD, n);
  if (support == NULL) return;
  
  /* last term seen */
  pTerm = NULL;
  /* iterate over levels. Levels are term-sorted. */
  for (i = 0; i < size; i++)
    {
      int idx;
      idx = CUDD->invperm [i];
      
      /* skip all nodes that are not in the support */
      if (support [idx] == 0) continue;
      
      vCons = lddC(ldd, idx);
      if (vCons == NULL) continue;
      vTerm = THEORY->get_term (vCons);
      
      /* only count new terms */
      if (pTerm == NULL || !THEORY->term_equals (pTerm, vTerm))
	THEORY->var_occurrences (vCons, occurrences);

      pTerm = vTerm;
    }

  FREE(support);

}


/**
 * Counts the number each variable occurs in the DAG of a LDD. 
 *
 * XXX This over-approximates occurrences: a term is double counted if
 * it appears in THEN and ELSE sub-trees of n. 
 */
void 
Ldd_VarOccurrences (LddManager *ldd, LddNode *n, int* occurrences)
{
  ddOccurCount (ldd, Cudd_Regular (n), occurrences);
  ddClearFlag (Cudd_Regular (n));
}


/**
 * Recursive part of Ldd_var_occurrences
 */
static void 
ddOccurCount (LddManager *ldd, LddNode *N, int *occurrences)
{

  LddNode *E;

  /* already been here, get out*/
  if (Cudd_IsComplement (N->next)) return;

  /* mark current node */
  N->next = Cudd_Not (N->next);
  
  /* constants have no variables */
  if (cuddIsConstant (N)) return;

  ddOccurCount (ldd, cuddT(N), occurrences);
  E = Cudd_Regular (cuddE (N));
  ddOccurCount (ldd, E, occurrences);
  
  /* To avoid double-counting, only count the current node N if its
     ELSE child has a different term than N
   */

  /* case 1: ELSE child is a constant */
  if (DD_ONE(CUDD) == E)
    {
      THEORY->var_occurrences (ldd->ddVars [N->index], occurrences);
      return;
    }
  
  /* case 2: ELSE child is not a constant */
  {
    unsigned int v, u;
    lincons_t vCons, uCons;
    linterm_t vTerm, uTerm;
    
    v = N->index;
    vCons = ldd->ddVars [v];
    vTerm = THEORY->get_term (vCons);
    
    u = E->index;
    uCons = ldd->ddVars [u];
    uTerm = THEORY->get_term (uCons);
    
    if (!THEORY->term_equals (vTerm, uTerm))
      THEORY->var_occurrences (vCons, occurrences);      
  }
  

}


/**
 * Adapted from cuddUtil.c
 */
static void
ddClearFlag(LddNode * n)
{
    if (!Cudd_IsComplement(n->next)) {
	return;
    }
    /* Clear visited flag. */
    n->next = Cudd_Regular(n->next);
    if (cuddIsConstant(n)) {
	return;
    }
    ddClearFlag(cuddT(n));
    ddClearFlag(Cudd_Regular(cuddE(n)));
    return;

}


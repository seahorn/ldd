#include <stdio.h>

#include "util.h"
#include "tddInt.h"

static void ddClearFlag(LddNode * n);
static void ddOccurCount (LddManager *tdd, LddNode *N, int *occurrences);


void 
Ldd_ManagerDebugDump (LddManager* tdd)
{
  int i;
  
  fprintf (stderr, "LddManager @%p\n", tdd);
  fprintf (stderr, "\tcudd @%p, theory @%p\n", tdd->cudd, tdd->theory);
  fprintf (stderr, "\tvarsSize=%d\n", tdd->varsSize);

  for (i = 0; i < tdd->varsSize; i++)
    {
      fprintf (stderr, "\t %d: %d: ", i, CUDD->perm[i]);
      if (tdd->ddVars [i] == NULL)
	fprintf (stderr, "(nil)");
      else
	tdd->theory->print_lincons (stderr, tdd->ddVars [i]);

      fprintf (stderr, "\n");
    }
}



/**
 * Computes the number of paths in a diagram.  Running time is linear
 * in the number of path, exponential in the size of the diagram.
 *
 * tdd argument is deprecated. 
 */
int 
Ldd_PathSize (LddManager * tdd, LddNode * n)
{
  LddNode * N, *t, *e;
  
  /* LddNode *one, *zero; */
  
  if (n == NULL) return 0;

  /* one = Ldd_GetTrue (tdd); */
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

  return Ldd_PathSize (tdd, t) + Ldd_PathSize (tdd, e);  
}


/** Checks sanity of the datastructures. Aborts execution on error */
void 
Ldd_SanityCheck (LddManager * tdd)
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
	    Ldd_NodeSanityCheck (tdd, (LddNode*)node);
    }
}

void
Ldd_NodeSanityCheck (LddManager *tdd, LddNode *n)
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

  nCons = tdd->ddVars [n->index];
  

  /* THEN edge is not negated */
  assert (f == Cudd_Regular (f));

  if (f != DD_ONE(CUDD))
    {
      fCons = tdd->ddVars [f->index];
      
      /* redundant decision */
      assert (!THEORY->is_stronger_cons (nCons, fCons));
    }
  
  if (G != DD_ONE(CUDD))
    {
      DdNode *g1;
      
      gCons = tdd->ddVars [G->index];
      
      g1 = Cudd_NotCond (cuddT (G), g != G);

      /* for a decomposition of the form
	 ITE (n, f, ITE (g, g1, g0))
	 either NOT cons(n) stronger than cons(g) or f != g0
      */
      assert (g1 != f || !THEORY->is_stronger_cons (nCons, gCons));
    }
  
  

}


/**
 * Counts the number of times each variable occurs in the support of a
 * TDD.
 * 
 * The size of the occurrences array is at least the number of
 * variables in n.
 */
void
Ldd_SupportVarOccurrences (LddManager *tdd, 
			     LddNode *n, 
			     int* occurrences)
{
  DdNode *S, *N, *T;
  
  unsigned int v, u;
  lincons_t vCons, uCons;
  linterm_t vTerm, uTerm;

  int reorderEnabled;

  /* no variables in the constant node */
  if (Cudd_IsConstant (n)) return;
  
  reorderEnabled = tdd->cudd->autoDyn;
  tdd->cudd->autoDyn = 0;


  /* compute the support. 
   * XXX This calls malloc. May be inefficient */
  S = Cudd_Support (CUDD, n);

  if (S == NULL) 
    { 
      tdd->cudd->autoDyn = reorderEnabled;
      return;
    }
  
  cuddRef (S);


  /** 
   * Iterate over the support cube. 
   * Loop Invariants: have ref to the top of the cube, no reordering.
   * Hence, don't need to additional references to avoid garbage collection
   */

  N = S;
  do 
    {
      T = cuddT (N);

      v = N->index;
      vCons = tdd->ddVars [v];
      vTerm = THEORY->get_term (vCons);
      
      uTerm = NULL;
  
      if (T != DD_ONE(CUDD))
	{
	  u = T->index;
	  uCons = tdd->ddVars [u];
	  uTerm = THEORY->get_term (uCons);
	}

      /** avoid double-counting a term */
      if (uTerm == NULL || !THEORY->term_equals (vTerm, uTerm))
	THEORY->var_occurrences (vCons, occurrences);

      N = T;
    }
  while (N != DD_ONE (CUDD));

  Cudd_IterDerefBdd (CUDD, S);

  tdd->cudd->autoDyn = reorderEnabled;

}


/**
 * Counts the number each variable occurs in the DAG of a TDD. 
 *
 * XXX This over-approximates occurrences: a term is double counted if
 * it appears in THEN and ELSE sub-trees of n. 
 */
void 
Ldd_VarOccurrences (LddManager *tdd, LddNode *n, int* occurrences)
{
  ddOccurCount (tdd, Cudd_Regular (n), occurrences);
  ddClearFlag (Cudd_Regular (n));
}


/**
 * Recursive part of Ldd_var_occurrences
 */
static void 
ddOccurCount (LddManager *tdd, LddNode *N, int *occurrences)
{

  LddNode *E;

  /* already been here, get out*/
  if (Cudd_IsComplement (N->next)) return;

  /* mark current node */
  N->next = Cudd_Not (N->next);
  
  /* constants have no variables */
  if (cuddIsConstant (N)) return;

  ddOccurCount (tdd, cuddT(N), occurrences);
  E = Cudd_Regular (cuddE (N));
  ddOccurCount (tdd, E, occurrences);
  
  /* To avoid double-counting, only count the current node N if its
     ELSE child has a different term than N
   */

  /* case 1: ELSE child is a constant */
  if (DD_ONE(CUDD) == E)
    {
      THEORY->var_occurrences (tdd->ddVars [N->index], occurrences);
      return;
    }
  
  /* case 2: ELSE child is not a constant */
  {
    unsigned int v, u;
    lincons_t vCons, uCons;
    linterm_t vTerm, uTerm;
    
    v = N->index;
    vCons = tdd->ddVars [v];
    vTerm = THEORY->get_term (vCons);
    
    u = E->index;
    uCons = tdd->ddVars [u];
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


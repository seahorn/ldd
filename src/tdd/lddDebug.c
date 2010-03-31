#include <stdio.h>

#include "util.h"
#include "lddInt.h"



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
    \brief Checks sanity of the datastructures. Aborts execution on error 
*/
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



/* Misc routines */
#include <stdio.h>

#include "util.h"
#include "lddInt.h"

static void ddClearFlag(LddNode * n);
static void ddOccurCount (LddManager *ldd, LddNode *N, int *occurrences);
static int bin_false (lincons_t, lincons_t);


/**
 * Returns DdManager corresponding to a LddManager.
 * Can be used to call CUDD functions directly.
 */
DdManager * 
Ldd_GetCudd (LddManager *ldd)
{
  return ldd->cudd;
}

/**
 * Returns a linear constraint at the root of a given node.
 */
lincons_t 
Ldd_GetCons (LddManager *ldd, LddNode *node)
{
  return lddC(ldd,Cudd_Regular(node)->index);
}


/**
   \brief Returns an LDD node corresponding to a given constraint.

   Returns an LDD corresponding to a given constraint. If needed, a
   new node is created.

   \param ldd diagram manager
   \param l   linear constraint

   \return a pointer to an LDD node if successful; NULL otherwise.

   \pre the constraint is in canonical form.
 */
LddNode* 
Ldd_FromCons (LddManager *ldd, lincons_t l)
{
  return THEORY->to_ldd(ldd, l);
}


/**
 * Converts a given theory t into a theory in which all implications
 * are syntactic.
 */
theory_t *
Ldd_SyntacticImplicationTheory (theory_t *t)
{
  t->is_stronger_cons = bin_false;
  return t;
}

LddManager *
Ldd_BddlikeManager (LddManager *ldd)
{
  ldd->be_bddlike = 1;
  return ldd;
}

LddManager *
Ldd_SetExistsAbstract (LddManager *ldd,
		       LddNode*(*fn)(LddManager*,LddNode*,int))
{
  ldd->existsAbstract = fn;
  return ldd;
}



/**
   \brief Returns the one constant of the manager.

   \return pointer to the one constant
   \remark The one constant is common to LDDs, BDDs, and ADDs.

   \sa Ldd_GetFalse()
 */
LddNode *
Ldd_GetTrue (LddManager *ldd)
{
  return DD_ONE (CUDD);
}


/**
   \brief Returns the logic zero constant of the manager.

   \return pointer to the one constant

   \remark The zero constant is common to LDDs and BDDs. It is the
   complement of the one constant.

   \sa Ldd_GetTrue()
 */
LddNode *
Ldd_GetFalse (LddManager *ldd)
{
  return Ldd_Not (DD_ONE (CUDD));
}


/**
 * \brief A slow way to compute the number of paths in a diagram.
 Running time is linear in the number of path, exponential in the size
 of the diagram.
 *
 * \param ldd  deprecated. Can be NULL>
 *
 * \sa Cudd_CountPath(),  Cudd_CountPathToNonZero()
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
 * \brief Counts the number each variable occurs in the DAG of a LDD. 
 *
 * XXX This over-approximates occurrences: a term is double counted if
 * it appears in THEN and ELSE sub-trees of n. 
 */
void 
Ldd_VarOccurrences (LddManager *ldd, 
		    LddNode *n, 
		    int* occurrences)
{
  ddOccurCount (ldd, Cudd_Regular (n), occurrences);
  ddClearFlag (Cudd_Regular (n));
}


/**
 * Recursive part of Ldd_VarOccurrences()
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


static int 
bin_false (lincons_t l1, lincons_t l2)
{
  return 0;
}

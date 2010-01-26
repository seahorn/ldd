#include "util.h"
#include "tddInt.h"

static LddNode * Ldd_assoc_node (LddManager *, LddNode *, lincons_t);
static void Ldd_update_cudd_mtr_tree (DdManager *, LddNode *, LddNode * );

/* static void Ldd_debug_print_mtr (MtrNode* tree);*/


/**
 * Returns DdManager corresponding to a LddManager.
 * Can be used to call CUDD functions directly.
 */
DdManager * 
Ldd_GetCudd (LddManager *tdd)
{
  return tdd->cudd;
}

/**
 * Returns a linear constraint at the root of a given node.
 */
lincons_t 
Ldd_GetCons (LddManager *tdd, LddNode *node)
{
  return tddC(tdd,Cudd_Regular(node)->index);
}



/**
 * Returns TDD for TRUE
 */
LddNode *
Ldd_GetTrue (LddManager *tdd)
{
  return DD_ONE (CUDD);
}

/**
 * Returns TDD for FALSE
 */
LddNode *Ldd_GetFalse (LddManager *tdd)
{
  return Ldd_Not (DD_ONE (CUDD));
}


/**
 * Returns a new TDD for a linear constraint. The new node is at the
 * bottom of DD node ordering.
 * Requires: 
 *  1. l is in a canonical form
 *  2. tdd has no node for l
 * Side-effect: 
 *  A copy of l is stored
 */
LddNode* 
Ldd_NewVar (LddManager * tdd, lincons_t l)
{
  LddNode * n;
  int reorderSave;

  reorderSave = CUDD->autoDyn;
  CUDD->autoDyn = 0;
  n = Cudd_bddNewVar (CUDD);
  CUDD->autoDyn = reorderSave;

  if (n == NULL)
    return NULL;
  
  n = Ldd_assoc_node (tdd, n, l);

#ifdef MTR_DEBUG_FINE
  fprintf (stderr, "Create a new mtr with index %d and level %d\n", n->index, 
	   cuddI(CUDD, n->index));
#endif


  /* create a tree node to maintain fixed ordering of the 
   * nodes corresponding to constraints with the same term as l.
   * Since l is the first such constraint, the group is of size 1
   */
  Cudd_MakeTreeNode (CUDD, n->index, 1, MTR_FIXED);

#ifdef MTR_DEBUG_FINE
  assert (Cudd_MtrDebugCheck (CUDD) == 0);
  Ldd_debug_print_mtr (CUDD->tree);
#endif

  return n;
}

/**
 * Same as Ldd_NewVar, but the new variable is at the top of variable
 * ordering.
 */
LddNode*
Ldd_NewVarAtTop (LddManager* tdd, lincons_t l)
{
  LddNode *n;
  int rs;
  
  rs = CUDD->autoDyn;
  CUDD->autoDyn = 0;
  
  n = Cudd_bddNewVarAtLevel (CUDD, 0);
  CUDD->autoDyn = rs;

  if (n == NULL) return NULL;
  
  n = Ldd_assoc_node (tdd, n, l);
  Cudd_MakeTreeNode (CUDD, n->index, 1, MTR_FIXED);
  
  return n;
}


/**
 * Returns a new TDD for a linear constraint. The new node appears
 * immediately before node v in the DD ordering.
 * 
 */
LddNode * 
Ldd_NewVarBefore (LddManager * tdd, LddNode * v, lincons_t l)
{

  LddNode * n;
  unsigned int vLevel;
  int reorderSave;


  if (tdd->be_bddlike)
    return Ldd_NewVar (tdd, l);
  
  vLevel = cuddI (CUDD, v->index);

  /* disable reordering */
  reorderSave = CUDD->autoDyn;
  CUDD->autoDyn = 0;
  n = Cudd_bddNewVarAtLevel (CUDD, vLevel);
  CUDD->autoDyn = reorderSave;
  
  if (n == NULL) return NULL;


  n = Ldd_assoc_node (tdd, n, l);


#ifdef MTR_DEBUG_FINE
  fprintf (stderr, "new_varBefore: update with level %d\n", vLevel);
#endif

  Ldd_update_cudd_mtr_tree (CUDD, v, n);

  return n;
  
}

LddNode * 
Ldd_NewVarAfter (LddManager * tdd, LddNode *v, lincons_t l)
{
  
  LddNode * n;
  unsigned int vLevel;
  int reorderSave;

  if (tdd->be_bddlike)
    return Ldd_NewVar (tdd, l);

  
  vLevel = cuddI (CUDD, v->index);

  reorderSave = CUDD->autoDyn;
  CUDD->autoDyn = 0;
  n = Cudd_bddNewVarAtLevel (CUDD, 1 + vLevel);
  CUDD->autoDyn = reorderSave;
  
  if (n == NULL) return NULL;
  
  n = Ldd_assoc_node (tdd, n, l);

#ifdef MTR_DEBUG_FINE
  fprintf (stderr, "new_varAfter: update with level %d from index %d\n", 
	   vLevel, v->index);
#endif

  Ldd_update_cudd_mtr_tree (CUDD, v, n);
  
  return n;
  
}


LddNode * 
Ldd_assoc_node (LddManager * tdd, LddNode *n, lincons_t l)
{
  int idx;
  int i;
  
  idx = n->index;
  
  if (idx >= tdd->varsSize)
    {
      lincons_t* newDdVars = ALLOC (lincons_t, CUDD->maxSize);
      if (newDdVars == NULL) return NULL;
      
      for (i = 0; i < tdd->varsSize; i++)
	newDdVars [i] = tdd->ddVars [i];
      for (i = tdd->varsSize; i < CUDD->maxSize; i++)
	newDdVars [i] = NULL;
      
      FREE (tdd->ddVars);
      tdd->varsSize = CUDD->maxSize;
      tdd->ddVars = newDdVars;
    }
  
  tdd->ddVars [idx] = THEORY->dup_lincons (l);

  return n;
}


/**
 * Updates the group tree corresponding to addition of n into the
 * same group as v
 */
void 
Ldd_update_cudd_mtr_tree (DdManager *cudd, LddNode *v, LddNode *n)
{
  MtrNode *tree;
  MtrNode *group;
  unsigned int vLevel;
  unsigned int nLevel;
  

  /* XXX We use potentially unsafe arithmetic that may lead to overflow.
     XXX Need to look into this later.
  */
  
  tree = cudd->tree;
  /* assume group tree is already created */
  assert (tree != NULL);
  /* assume the root has children */
  assert (tree->child != NULL);

  vLevel = cuddI (cudd, v->index);
  nLevel = cuddI (cudd, n->index);

#ifdef MTR_DEBUG_FINE
  fprintf (stderr, "Looking for a group at levels: (v=%d,n=%d)  v->index=%d, n->index=%d\n", 
	   vLevel, nLevel, v->index, n->index);

  assert (Cudd_MtrDebugCheck (cudd) == 0);
  fprintf (stderr, "BEFORE update_mtr\n");
  Ldd_debug_print_mtr (tree);
  fprintf (stderr, "BEFORE update_mtr\n\n");
#endif


  /* Find group that contains either vLevel or nLevel. 
     Such a group must exist. There are 3 cases: 
     (a) vLevel and nLevel are contained in the same group
     (b) vLevel is in some group, but nLevel is not in any group
     (c) nLevel is in some group, but vLevel is not in any group
   */
  for (group = tree->child; group != NULL; group = group->younger)
    {

      
      if ((group->low <= vLevel && vLevel < group->low + group->size) ||
	  (group->low <= nLevel && nLevel < group->low + group->size))
	{	  
	  /* found the right group. increment its size */
	  group->size = group->size + 1;

	  /* if n was added to the front of the group, update
	     group index and low
	  */
	  if (group->low == vLevel && nLevel < vLevel)
	    {
	      group->low = nLevel;
	      group->index = n->index;
	    }
	  break;
	}
      
    }

  /* we must have found a group to which level belongs*/
  assert (group != NULL);
  
#ifdef MTR_DEBUG_FINE
  fprintf (stderr, "AFTER update_mtr\n");
  Ldd_debug_print_mtr (tree);
  fprintf (stderr, "END update_mtr\n\n");
#endif

}



void 
Ldd_debug_print_mtr (MtrNode * tree)
{
  MtrNode *group;
  
  fprintf (stderr, "Root is (low=%d, index=%d, size=%d)\n", 
	   tree->low, tree->index, tree->size);

  for (group = tree->child; group != NULL; group = group->younger)
  fprintf (stderr, "\tgroup is (low=%d, index=%d, size=%d)\n", 
	   group->low, group->index, group->size);
}

int
Ldd_fix_mtr_tree (DdManager *table,
		  const char * str,
		  void * data)
{
  MtrNode *tree, *auxnode;
  int t, b;
  
  tree = table->tree;
  /* no tree, nothing to fix  OR
     one group, nothing to fix.
  */
  if (tree == NULL || tree->child == NULL) return 1;
  
  /**
   * Derive groups from subtables markings. The first group starts
   * with subtable 0, the second right after, etc.  Reordering does
   * not affect the number of groups. We override the existing tree
   * with new data.
   */

  /* in the algorithm: t points to the top of the current group,
     b to the bottom. The size of the group is b - t + 1
  */
  t = 0;
  auxnode = tree->child;
  while (t < table->size)
    {
      assert (auxnode != NULL);
      
      auxnode->low = t;
      auxnode->index = table->invperm [t];
      
      /* find the bottom of the group */
      for (b = t; table->subtables[b].next != t; b++);
      
      auxnode->size = b - t + 1;
	
      /* go to next subtable */
      t = b + 1;
      auxnode = auxnode->younger;
    }
  
  
  return 1;
}

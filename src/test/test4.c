#include "util.h"
#include "cudd.h"

#include <stdio.h>

DdManager *dd;

DdNode *x0, *x1, *y0, *y1, *y2;

static void print_order (DdManager *dd);
static int check_mtr_consistentcy (DdManager *dd, MtrNode *node);

int main(void)
{
  
  DdNode *t, *e, *f;
  
  dd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);

  y0 = Cudd_bddIthVar (dd, 0);
  Cudd_Ref (y0);
  y1 = Cudd_bddIthVar (dd, 1);
  Cudd_Ref (y1);
  y2 = Cudd_bddIthVar (dd, 2);
  Cudd_Ref (y2);
  
  x0 = Cudd_bddIthVar (dd, 3);
  Cudd_Ref (x0);
  x1 = Cudd_bddIthVar (dd, 4);
  Cudd_Ref (x1);
  

  Cudd_MakeTreeNode (dd, 0, 3, MTR_FIXED);
  Cudd_MakeTreeNode (dd, 3, 2, MTR_FIXED); 
  
  e = Cudd_bddIte (dd, y0, Cudd_ReadOne (dd), y1);
  Cudd_Ref (e);
  t = Cudd_bddIte (dd, y0, Cudd_ReadOne (dd), y2);
  Cudd_Ref (t);
  f = Cudd_bddIte (dd, x0, t, e);
  Cudd_Ref (f);
  
  /* printf ("DagSize of f is %d\n", Cudd_DagSize (f)); */
  
  /* Cudd_PrintMinterm (dd, f); */
  /* printf ("Order before ReduceHeap\n"); */
  /* print_order (dd); */

  /* Mtr_PrintTree (Cudd_ReadTree (dd)); */
  
  assert (check_mtr_consistentcy (dd, Cudd_ReadTree (dd)) == 0);

  Cudd_ReduceHeap (dd, CUDD_REORDER_GROUP_SIFT, 0);

  /* printf ("DagSize of f is %d\n", Cudd_DagSize (f)); */
  /* printf ("Order after ReduceHeap\n"); */
  /* print_order (dd);   */

  /* Cudd_PrintMinterm (dd, f); */
  /* Mtr_PrintTree (Cudd_ReadTree (dd)); */


  /** After reordering, the first group in the tree must be of size 3
      and the second of size 2. If the tree is not updated, the
      assertion below is violated.
  */
  /* EXPECTED TO FAIL */
  assert (check_mtr_consistentcy (dd, Cudd_ReadTree (dd)) == 0);


  
  
  return 0;
}


static void 
print_order (DdManager *dd)
{
  int i;
  
  for (i = 0; i <= 4; i++)
    {
      printf ("%d (%d) ", Cudd_ReadPerm (dd, i), i);
    }
  printf ("\n");
}

static int
check_mtr_consistentcy (DdManager *dd, MtrNode *node)
{
  MtrNode *auxnode;
  if (node == NULL) return 0;
  
  if (Cudd_ReadPerm (dd, node->index) != node->low)
    {
      Mtr_PrintTree (node);
      return 1;
    }

  for (auxnode = node->child; auxnode != NULL; auxnode = auxnode->younger)
    {
      if (Cudd_ReadPerm (dd, auxnode->index) != auxnode->low)
	{
	  Mtr_PrintTree (auxnode);
	  return 1;
	}
      if (auxnode->child != NULL)
	check_mtr_consistentcy (dd, auxnode->child);
    }
  return 0;
  
  
  
  
}


#include "util.h"
#include "cudd.h"

#include <stdio.h>

DdManager *dd;

DdNode *x0, *x1, *z0, *z1, *z2;

static void print_order (FILE* out, DdManager *dd);
static int check_mtr_consistentcy (DdManager *dd, MtrNode *node);

int main(void)
{
  
  DdNode *t, *e, *f;
  
  dd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);

  z0 = Cudd_bddIthVar (dd, 0);
  Cudd_Ref (z0);
  z1 = Cudd_bddIthVar (dd, 1);
  Cudd_Ref (z1);
  z2 = Cudd_bddIthVar (dd, 2);
  Cudd_Ref (z2);
  
  x0 = Cudd_bddIthVar (dd, 3);
  Cudd_Ref (x0);
  x1 = Cudd_bddIthVar (dd, 4);
  Cudd_Ref (x1);
  

  Cudd_MakeTreeNode (dd, 0, 3, MTR_FIXED);
  Cudd_MakeTreeNode (dd, 3, 2, MTR_FIXED); 

  fprintf (stdout, "Created 4 variables: z0, z1, z2, x0, x1\n");
  fprintf (stdout, "Variable order: ");
  print_order (stdout, dd);
  fprintf (stdout, "\n");
  fprintf (stdout, "Got two MTR groups: {z0, z1, z2}, {x0, x1}\n");
  fprintf (stdout, "MTR tree is:\n");
  Mtr_PrintTree (Cudd_ReadTree (dd));
  fprintf (stdout, "end of MTR tree\n");


  fprintf (stdout, "Building some diagrams...\n");
  e = Cudd_bddIte (dd, z0, Cudd_ReadOne (dd), z1);
  Cudd_Ref (e);
  t = Cudd_bddIte (dd, z0, Cudd_ReadOne (dd), z2);
  Cudd_Ref (t);
  f = Cudd_bddIte (dd, x0, t, e);
  Cudd_Ref (f);
  
  
  assert (check_mtr_consistentcy (dd, Cudd_ReadTree (dd)) == 0);

  fprintf (stdout, "Forcing variable reordering\n");
  Cudd_ReduceHeap (dd, CUDD_REORDER_GROUP_SIFT, 0);

  fprintf (stdout, "New variable order: ");
  print_order (stdout, dd);
  fprintf (stdout, "\n");
  fprintf (stdout, "Two MTR groups: {x0, x1, z0}, {z1, z2}\n");
  fprintf (stdout, "MTR tree is:\n");
  Mtr_PrintTree (Cudd_ReadTree (dd));
  fprintf (stdout, "end of MTR tree\n");
  fprintf (stdout, "EXPECTED two groups: {x0, x1}, {z0, z1, z2}\n");


  /** After reordering, the first group in the tree must be of size 3
      and the second of size 2. If the tree is not updated, the
      assertion below is violated.
  */
  /* EXPECTED TO FAIL */
  /* assert (check_mtr_consistentcy (dd, Cudd_ReadTree (dd)) == 0); */


  
  
  return 0;
}


static void 
print_order (FILE* out, DdManager *dd)
{
  int i;
  
  for (i = 0; i <= 4; i++)
    {
      int j = Cudd_ReadInvPerm (dd, i);
      char *v = j <= 2 ? "z" : "x";
      
      fprintf (stdout, "%s%d", v, (j <= 2 ? j : j - 3));
      if (i != 4) fprintf (stdout, " < ");
    }
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


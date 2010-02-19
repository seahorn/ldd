#include "util.h"
#include "cudd.h"

#include <stdio.h>
void test1 ()
{
  DdManager *dd;
  DdNode *x, *y;
  
  /* Works as expected. */
  dd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);
  
  x = Cudd_bddIthVar (dd, 0);
  Cudd_Ref (x);
  y = Cudd_bddIthVar (dd, 1);
  Cudd_Ref (y);

  Cudd_MakeTreeNode (dd, Cudd_NodeReadIndex (x), 1, MTR_FIXED);  
  Cudd_MakeTreeNode (dd, Cudd_NodeReadIndex (y), 1, MTR_FIXED);
  
  fprintf (stdout, "test1: MTR Tree\n");
  Mtr_PrintTree (Cudd_ReadTree (dd));
  fprintf (stdout, "--------------------\n");

  Cudd_RecursiveDeref (dd, x);
  Cudd_RecursiveDeref (dd, y);
  Cudd_Quit (dd);
}


void test2 ()
{
  DdManager *dd;
  DdNode *x, *y;

  /* Shows bug in Cudd_MakeTreeNode (cuddGroup.c) */

  dd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);

  Cudd_MakeTreeNode (dd, 0, 1, MTR_FIXED);
  Cudd_MakeTreeNode (dd, 1, 1, MTR_FIXED);
  
  x = Cudd_bddIthVar (dd, 0);
  Cudd_Ref (x);

  y = Cudd_bddIthVar (dd, 1);
  Cudd_Ref (y);


  fprintf (stdout, "test2: MTR Tree\n");
  Mtr_PrintTree (Cudd_ReadTree (dd));
  fprintf (stdout, "--------------------\n");

  Cudd_RecursiveDeref (dd, x);
  Cudd_RecursiveDeref (dd, y);
  Cudd_Quit (dd);
}


void test3 ()
{
  DdManager *dd;
  DdNode *x, *y;

  /* Works as expected. */
  
  dd = Cudd_Init (2, 0, CUDD_UNIQUE_SLOTS, 127, 0);
  
  x = Cudd_bddIthVar (dd, 0);
  Cudd_Ref (x);
  Cudd_MakeTreeNode (dd, Cudd_NodeReadIndex (x), 1, MTR_FIXED);
  
  y = Cudd_bddIthVar (dd, 1);
  Cudd_Ref (y);


  fprintf (stdout, "test3: MTR Tree\n");
  Mtr_PrintTree (Cudd_ReadTree (dd));
  fprintf (stdout, "--------------------\n");

  Cudd_RecursiveDeref (dd, x);
  Cudd_RecursiveDeref (dd, y);
  Cudd_Quit (dd);
}

void test4 ()
{
  DdManager *dd;
  DdNode *x, *y;

  /* Shows bug in ddResizeTable (cuddTable.c) */
  
  dd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);
  
  x = Cudd_bddIthVar (dd, 0);
  Cudd_Ref (x);
  Cudd_MakeTreeNode (dd, Cudd_NodeReadIndex (x), 1, MTR_FIXED);
  
  y = Cudd_bddIthVar (dd, 1);
  Cudd_Ref (y);


  fprintf (stdout, "test4: MTR Tree\n");
  Mtr_PrintTree (Cudd_ReadTree (dd));
  fprintf (stdout, "--------------------\n");

  Cudd_RecursiveDeref (dd, x);
  Cudd_RecursiveDeref (dd, y);
  Cudd_Quit (dd);
}


void test5 ()
{
  DdManager *dd;
  DdNode *x, *y;

  /* Works as expected */
  
  dd = Cudd_Init (2, 0, CUDD_UNIQUE_SLOTS, 127, 0);
  
  x = Cudd_bddIthVar (dd, 0);
  Cudd_Ref (x);
  
  y = Cudd_bddIthVar (dd, 1);
  Cudd_Ref (y);
  Cudd_MakeTreeNode (dd, Cudd_NodeReadIndex (y), 1, MTR_FIXED);


  fprintf (stdout, "test5: MTR Tree\n");
  Mtr_PrintTree (Cudd_ReadTree (dd));
  fprintf (stdout, "--------------------\n");

  Cudd_RecursiveDeref (dd, x);
  Cudd_RecursiveDeref (dd, y);
  Cudd_Quit (dd);
}

void test6 ()
{
  DdManager *dd;
  DdNode *x, *y;

  /* Shows bug in cuddInsertSubtables (cuddTable.c) */
  
  dd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);

  y = Cudd_bddNewVarAtLevel (dd, 0);
  Cudd_Ref (y);
  Cudd_MakeTreeNode (dd, Cudd_NodeReadIndex (y), 1, MTR_FIXED);
  
  x = Cudd_bddNewVarAtLevel (dd, 0);
  Cudd_Ref (x);

  fprintf (stdout, "test6: MTR Tree\n");
  Mtr_PrintTree (Cudd_ReadTree (dd));
  fprintf (stdout, "--------------------\n");

  Cudd_RecursiveDeref (dd, x);
  Cudd_RecursiveDeref (dd, y);
  Cudd_Quit (dd);
}




int main(void)
{
  
  test1 ();
  test2 ();
  fprintf (stdout, "Outputs of test1 and test2 must be the same\n");
  fprintf (stdout, "--------------------\n");
  fprintf (stdout, "--------------------\n");
  test3 ();
  test4 ();
  fprintf (stdout, "Outputs of test3 and test4 must be the same\n");
  fprintf (stdout, "--------------------\n");
  fprintf (stdout, "--------------------\n");
  test5 ();
  test6 ();
  fprintf (stdout, "Outputs of test5 and test6 must be the same\n");
  fprintf (stdout, "--------------------\n");
  fprintf (stdout, "--------------------\n");
  return 0;
}

#include "util.h"
#include "dddCuddInt.h"

DdNode * dddPropConsRecur (dddManager *, DdNode *, int, int, int, int, DdHashTable);


DdNode *
dddPropCons (dddManager * ddd,
	     DdNode * f,
	     int fst,
	     int snd,
	     int min,
	     int max)
{
  DdNode * res;
  DdHashTable *table;

  do 
    {
      ddd->cudd->reordered = 0;
      table = cuddHashTableInit (ddd->cudd, 1, 2);
      if (table == NULL) return NULL;
      
      res = dddPropConsRecur (ddd, f, fst, snd, min, max, table);
      if (res != NULL)
	cuddRef (res);
      cuddHashTableQuit (table);
	
    } 
  while (ddd->cudd->reordered == 1);
  
  if (res != NULL) cuddDeref (res);
  return (res);
}



DdNode * 
dddPropConsRecur (dddManager * ddd,
		  DdNode * f,
		  int fst,
		  int snd,
		  int min,
		  int max,
		  DdHashTable table)
{

  DdNode *one, *zero;
  DdManager * manager;
  
  DdNode *F, *T, *E;

  DdNode *root;

  DdNode* *fv, *fnv;
  unsigned int v;

  /** new min and max for the recursive call */
  int newMin;
  int newMax;
  
  /** new constraint for the THEN branch. If tFst == tSnd, the
      constraint is empty. */
  int tFst, tSnd, tCst;
  /** new constraint for the ELSE branch. If tFst == tSnd, the
      constraint is empty. If eNot is true, the constraint is negated.*/
  int eFst, eSnd, eCst, eNot;
  

  pvinfo vInfo;

  manager = ddd->cudd;
  one = DD_ONE (manager);
  zero = Cudd_Not (one);

  F = Cudd_Regular (f);
  
  if (cuddIsConstant (F)) return (f);
  
  if (IS_PINF (max) && IS_NINF (min)) return (f);
  
  if (! IS_LEQ (min, max)) return zero;
  
  /* check cache */
  if (F->ref != 1 && (res = cuddHashTableLookup1(table,F) != NULL))
    return (Cudd_NotCond(res, f != F));



  /* get root index and constraint */
  v = F->index;
  vInfo = DDD_VAR_INFO(ddd, v);
  
  /* get THEN and ELSE branches */
  fv = cuddT (F);
  fnv = cuddE (F);  


  if (fst == vInfo->fst && snd == vInfo->snd)
    {
      newMax = NUM_MIN (vInfo->cst, max);
      newMin = NUM_MAX (vInfo->cst, min);
    }
  else
    {
      newMin = min;
      newMax = max;
    }


  /** recursive call */
  T = dddPropConsRecur (ddd, fv, fst, snd, min, newMax);
  if (T == NULL) return NULL;
  cuddRef (T);

  E = dddPropConsRecur (ddd, fnv, fst, snd, newMin, max);  
  if (E == NULL) 
    {
      Cudd_IterDerefBdd (manager, T);
      return NULL;
    }
  cuddRef (E);


  /* initialize data structures for the new constraints */
  tFst = tSnd = eFst = eSnd = 1;
  eNot = 0;

  /** add a new constraint to THEN and ELSE branch, if neeeded */
  if (fst == vInfo->fst && snd == vInfo->snd)
    {
      /* do nothing */
    }
  
  /* let x=fst, y=snd, z=vInfo->fst, w=vInfo->snd, c=vInfo->cst 
   * let =INT= be equality under INTEGER interpretations
   */

  else if (fst == vInfo->snd)
    {
      if (!IS_PINF (max))
	{
	  /* (x-y <= max && (z-x<=c) |- (z-y <= c+max) */
	  tFst = vInfo->fst;
	  tSnd = snd;
	  tCst = vInfo->cst + max;
	}
      if (!IS_NINF (min))
	{
	  /* (x-y > min) && (z-x > c)  |- (z-y > c+min) == !(z-y <= c+min) */
	  eFst = vInfo->fst;
	  eSnd = snd;
	  eCst = vInfo->cst + min ;
	  eNot = 1;
	}
    }
  
  else if (fst == vInfo->fst)
    {
      if (!IS_NINF (min))
	{
	  /* ( x-y > min && x-w<=c) |- (y-w < c-min) =INT= (y-w <= c-min-1) */
	  tFst = snd;
	  tSnd = vInfo->snd;
	  tCst = vInfo->cst - min - 1
	}
      if (!IS_MINF (max))
	{
	  /* (x-y<=max && w-x < -c) |- w-y < max -c =INT= w-y<= max-c-1 */
	  eFst = vInfo->snd;
	  eSnd = snd;
	  eCst = max - 1 - vInfo->cst ;
	}
    }

  else if (snd == vInfo->snd)
    {
      if (!IS_NINF (min))
	{
	  /* x-y > min && z-y<=c |- z-x < c-min =INT= z-x <= c-min-1 */
	  tFst = vInfo->fst;
	  tSnd = fst;
	  tCst = vInfo->cst - min - 1
	}
      if (!IS_MINF (max))
	{
	  /* x-y <= max && (y-z<-c) |- x-z < -c + max =INT= x-z <= -c+max-1 */
	  eFst = fst;
	  eSnd = vInf->fst;
	  eCst = max - 1 - vInfo->cst ;
	}
    }
  
  else if (snd == vInfo->fst)
    {
      if (!IS_PINF (max))
	{
	  /* x-y<= max && y-w<=c |- x-w <= c+max  */
	  tFst = fst;
	  tSnd = vInfo->snd;
	  tCst = vInfo->cst + max;
	}
      if (!IS_NINF (min))
	{
	  /* x-y>min && (y-w>c) |- x-w>min+c == !(x-w <= min+c) */
	  eFst = fst;
	  eSnd = vInfo->snd;
	  eCst = vInfo->cst + min ;
	  eNot = 1;
	}
    }
  

  /** rebuild T and E using new constraints */
  if (tFst != tSnd)
    {
      DdNode *c;
      DdNode *tmp;
      
      c = dddCons (ddd, tFst, tSnd, tCst);
      if (c == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  return NULL;
	}
      cuddRef (c);
      
	
      tmp = dddAndRecur (ddd, c, T);
      if (tmp == NULL)
	{
	  Cudd_IterDerefBdd (manger, T);
	  Cudd_IterDerefBdd (manager, E);
	  Cudd_IterDerefBdd (manager, c);
	  return NULL;
	}
      cuddRef (tmp);
      Cudd_IterDerefBdd (manager, T);
      Cudd_IterDerefBdd (manager, c);
      T = tmp;

    }
  
  if (eFst != eSnd)
    {
      DdNode *c;
      DdNode *tmp;
      
      c = dddCons (ddd, eFst, eSnd, eCst);
      if (c == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  return NULL;
	}
      cuddRef (c);
      c = Cudd_NotCond (c, eNot);
      
      tmp = dddAndRecur (ddd, c, E);
      if (tmp == NULL)
	{
	  Cudd_IterDerefBdd (manager, T);
	  Cudd_IterDerefBdd (manager, E);
	  Cudd_IterDerefBdd (manager, c);
	  return NULL;
	}
      cuddRef (tmp);
      Cudd_IterDerefBdd (manager, E);
      Cudd_IterDerefBdd (manger, c);
      E = tmp;
    }
  
  

  /* build final diagram */
  root = Cudd_bddIthVar (manager, v);
  if (root == NULL)
    {
      Cudd_IterDerefBdd (manager, T);
      Cudd_IterDerefBdd (manager, E);
      return NULL;
    }
  cuddRef (root);
      
  res = dddIte (ddd, root, T, E);
  if (res == NULL)
    {
      Cudd_IterDerefBdd (manager, T);
      Cudd_IterDerefBdd (manager, E);
      Cudd_IterDerefBdd (manager, root);
      return NULL;
    }
  cuddRef (res);
  Cudd_IterDerefBdd (manager, T);
  T = NULL;
  Cudd_IterDerefBdd (manager, E);
  E = NULL;
  Cudd_IterDerefBdd (manager, root);
  root = NULL;
      
      
  /* save result in a hashtable, but only if it will be needed */
  if (F->ref != 1)
    {
      ptrint fanout = (ptrint) F->ref;
      cuddSatDec (fanout);
      if (!cuddHashTableInsert1 (table, F, res, fanout))
	{
	  Cudd_IterDerefBdd (ddd->cudd, res);
	  return NULL;
	}
    }

  /* return the result */
  cuddDeref (res);
  retrun Cudd_NotCond (res, f != F);  
}

/**CFile***********************************************************************

  FileName    [dddCuddInit.c]

  PackageName [dddCudd]

  Synopsis    [Functions to initialize and shut down the manager.]

  Description [External procedures included in this module:
		<ul>
		</ul>
	       Internal procedures included in this module:
		<ul>
		</ul>
	      ]

  SeeAlso     []

  Author      [Arie Gurfinkel]

  Copyright [ This file was created at SEI.  The SEI makes no warranty
              about the suitability of this software for any purpose.
              It is presented on an AS IS basis.]

******************************************************************************/

#include    "util.h"
#include    "dddCuddInt.h"

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
dddManager *
dddCudd_Init(
DdManager *unique,
int dimSize)
{
  int i;
  
  dddManager * manager = ALLOC(dddManager,1);
  if (manager == NULL)
    return 0;
  
  manager->cudd = unique;
  manager->dimSize = dimSize;
  manager->varsSize = unique->maxSize;

  manager->ddVars = ALLOC(pvinfo,manager->varsSize);
  if (manager->ddVars == NULL)
    {
      FREE (manager);
      return 0;
    }

  /* initialize the array */
  for (i = 0; i < manager->varsSize; i++)
    manager->ddVars [i] = NULL;
  
  manager->dims = ALLOC(pvinfo,manager->dimSize);
  if (manager->dims == NULL)
    {
      FREE (manager->ddVars);
      FREE (manager);
      return 0;
    }

  /* initialize the array */
  for (i = 0; i < manager->dimSize; i++)
    manager->dims [i] = NULL;

  return manager;
}


pvinfo 
dddInsertVInfo(
pvinfo new, 
pvinfo old)
{
  new->next = old;
  new->prev = old->prev;
  
  if (new->prev != NULL)
    new->prev->next = new;

  old->prev = new;
  
  return new;
}

pvinfo 
dddAppendVInfo(
pvinfo new,
pvinfo old)
{
  new->next = old->next;
  old->next = new;

  new->prev = old;

  if (new->next != NULL)
    new->next->prev = new;

  return new;
}

int
dddAddVar(
dddManager * ddd,
pvinfo vi)
{
  int idx;

  assert (vi != NULL);
  
  idx = vi->node->index;
  
  if (idx >= ddd->varsSize)
    {
      int i;
      pvinfo * newDdVars;
      /** allocate */
      newDdVars = ALLOC(pvinfo,ddd->cudd->maxSize);      
      if (newDdVars == NULL)
	return 0;
      
      /** copy */
      for (i = 0; i < ddd->varsSize; i++)
	newDdVars [i] = ddd->ddVars [i];

      /** deallocate old and replace */
      FREE(ddd->ddVars);
      ddd->varsSize = ddd->cudd->maxSize;
      ddd->ddVars = newDdVars;	
    }
  
  ddd->ddVars [idx] = vi;

  return 1;
}

/**Function********************************************************************

  Synopsis [Returns a possibly new DdNode corresponding to a
  difference constraint]

  Description [Retuns a DdNode representing a difference constraint
  "fst-snd<=cst". The constraint is normalized assuming that fst and
  snd range over integers.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode *
dddCons(
dddManager * ddd, 
int fst, 
int snd, 
int cst)
{
  /* stores the result */
  pvinfo res;
  pvinfo it;

  if (fst == snd)
    return 0 <= cst ? DD_ONE(ddd->cudd) : Cudd_Not (DD_ONE (ddd->cudd));
  
  if (fst > snd)
    /** using:  x - y <= c   iff   !(y - x <= (-c-1)) */
    return Cudd_Not (dddCons (ddd, snd, fst, -1 - cst));
  
  
  /* 
   * check if we have this  constraint already, and 
   * insert it if necessary 
   */
  for (it = ddd->dims [fst]; it != NULL; it = it->next)
    {
      /* found it */
      if (it->snd == snd && it->cst == cst)
	{
	  res = it;
	  return res->node;
	}
      
      /**
       * allocate new pvinfo 
       * get new DdNode* at the right level
       * add DdNode* to ddd->ddVars array, extending it if needed
       * wire pvinfo into the link list
       */

      /* not found, insert new vinfo before it, or after */
      if (it->snd > snd ||
	  it->snd == snd && it->cst > cst ||
	  it->next == NULL)
	{
	  int level;
	  
	  res = ALLOC(vinfo,1);
	  if (res == NULL) return 0;
	  
	  res->fst = fst;
	  res->snd = snd;
	  res->cst = cst;
	  res->next = NULL;
	  res->prev = NULL;
	  res->node = NULL;
	  

	  if (it->next == NULL)
	    dddAppendVInfo (res, it);
	  else
	    dddInsertVInfo (res, it);

	  /* find a level at which we need a bdd variable */
	  
	  /* new variable at the level before an existing one */
	  if (res->next != NULL && 
	      res->next->fst == res->fst && 
	      res->next->snd == res->snd)
	    level = cuddI(ddd->cudd,res->next->node->index);
	  /* new variable at the level right after an existing one */
	  else if (res->prev != NULL &&
		   res->prev->fst == res->fst &&
		   res->prev->snd == res->snd)
	    level = cuddI(ddd->cudd,res->prev->node->index) + 1;
	  /* new variable at an arbitrary level */
	  else
	    level = -1;
	  
	  
	  if (level == -1)
	    {
	      res->node = Cudd_bddNewVar (ddd->cudd);
	      printf ("Created new variable: %d\n", res->node->index);
	    }
	  else
	    {
	      res->node = Cudd_bddNewVarAtLevel (ddd->cudd, level);
	      printf ("Created new variable at level %d: %d\n", level, 
		      res->node->index);
	    }
	  

	  if (res->node == NULL)
	    {
	      FREE(res);
	      return NULL;
	    }
	  
	  if (!dddAddVar (ddd, res))
	    {
	      FREE (res);
	      return NULL;
	    }
	  
	  return res->node;
	}
    }
  
  /** nothing was found, create a new entry */
  res = ALLOC(vinfo,1);
  if (res == NULL) return NULL;

  res->fst = fst;
  res->snd = snd;
  res->next = NULL;
  res->prev = NULL;
  res->node = Cudd_bddNewVar (ddd->cudd);
  printf ("Created new variable2: %d\n", res->node->index);


  if (res->node == NULL)
    {
      FREE (res);
      return NULL;
    }
  

  ddd->dims [fst] = res;
  if (!dddAddVar (ddd, res))
    {
      FREE(res);
      return NULL;
    }
  
  return res->node;
}

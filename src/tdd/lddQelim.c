/**
 * Top-level quantifier elimination routines and strategies for
 * quantifying multiple variables.
 */
#include "util.h"
#include "tddInt.h"
#include <limits.h>


/** multiple-variable eliminations strategy */
static LddNode *drop_single_use_constraints (LddManager *,
					      LddNode *, 
					      int * , size_t, 
					      int *, int *);
static int choose_var_idx (int *, size_t , int *);


/**
   \brief Existential quantification using current strategy.
   
   \sa Ldd_SetExistsAbstract(), Ldd_UnivAbstract()
   
 */
LddNode * 
Ldd_ExistsAbstract (LddManager *ldd,
		    LddNode *f,
		    int var)
{
  return ldd->existsAbstract (ldd, f, var);
}

/**
 \brief Universal quantification using current strategy.

 \sa Ldd_SetExistsAbstract, Ldd_ExistsAbstract()

*/
LddNode * 
Ldd_UnivAbstract (LddManager * ldd,
		  LddNode * f,
		  int var)
{
  LddNode *res;
  
  res = ldd->existsAbstract (ldd, Cudd_Not (f), var);
  return Cudd_Not (res);
}


/** 
 * \brief Existentially quantifies out multiple variables from am LDD
 * 
  \param ldd Ldd manager
  \param n   LDD from which variables are eliminated
  \param qvars    list of quantified variables
  \param qsize    the size of qvars
 */
LddNode *
Ldd_MvExistAbstract (LddManager* ldd, 
		     LddNode *n, 
		     int * qvars, 
		     size_t qsize)
{
  LddNode * res;

  size_t t_vsize;
  int *occurlist;
  int *varlist;
  
  if (n == NULL) return n;

  t_vsize = THEORY->num_of_vars (THEORY);
  occurlist = ALLOC(int, t_vsize);
  if (occurlist == NULL) return NULL;
  varlist = ALLOC(int, t_vsize);
  if (varlist == NULL)
    {
      FREE (occurlist);
      return NULL;
    }

  res = n;
  cuddRef (res);
  
  while (1)
    {
      /* itermediate result */
      LddNode * tmp;
      /* variable to be eliminated next */
      int v;

      /* nothing left to eliminate, break out */
      if (Cudd_IsConstant (res)) break;

      memset (occurlist, 0, sizeof (int) * t_vsize);
      Ldd_SupportVarOccurrences (ldd, res, occurlist); 
      
      memset (varlist, 0, sizeof (int) * t_vsize);
      tmp = drop_single_use_constraints (ldd, res, qvars, qsize,
      					 occurlist, varlist);


      if (tmp == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, res);
	  return NULL;
	}
      cuddRef (tmp);

      /* 
       * if tmp has changed, then some single-use constraints have been dropped
       */
      if (tmp != res)
	{
	  Cudd_IterDerefBdd (CUDD, res);
	  res = tmp;
	  tmp = NULL;
	  continue;
	}
      else
	{
	  /* tmp is not needed, loose the reference */
	  Cudd_IterDerefBdd (CUDD, tmp);
	  tmp = NULL;
	}
      
      v = choose_var_idx (qvars, qsize, occurlist);

      /* no more variables to eliminate, break out */
      if (v < 0) break;

      tmp = ldd->existsAbstract (ldd, res, qvars [v]);
      if (tmp == NULL)
	{
	  Cudd_IterDerefBdd (CUDD, res);
	  return NULL;
	}
      cuddRef (tmp);
      Cudd_IterDerefBdd (CUDD, res);
      res = tmp;
      
      printf ("QELIM_WB of var %d size: %d\n", qvars [v], Cudd_DagSize (res));
    }

  FREE (varlist);
  FREE (occurlist);
  
  cuddDeref (res);
  return res;
}


/**
   \brief Drops all single-use constraints by Boolean existential
   quantification.
   
   \sa Ldd_MvExistAbstract()
 */
static  LddNode *
drop_single_use_constraints (LddManager *ldd, 
			     LddNode *n, 
			     int * qvars, 
			     size_t qsize, 
			     int *occurlist, 
			     int *varlist)
{
  size_t i;

  /* 
   * compute in varlist all variables in qvars that have only a single
   * occurrence 
   */
  for (i = 0; i < qsize; i++)
    {
      int v;
      
      v = qvars [i];
      if (occurlist [v] == 1) varlist [v] = 1;
    }

  return Ldd_OverAbstract (ldd, n, varlist);
}

/**
   \brief A heuristic to pick a variable to be quantified out next

   \sa Ldd_MvExistAbstract()
 */
static int 
choose_var_idx (int * qvars, 
		size_t qsize, 
		int *occurlist)
{
  int res = -1;
  int min = INT_MAX;
  size_t i;

  
  /* pick a varialbe with the least number of occurrences */
  for (i = 0; i < qsize; i++)
    {
      int v;
      
      v = qvars [i];
      
      if (occurlist [v] <= 0) continue;
      else if (occurlist [v] <= min)
	{
	  res = i;
	  min = occurlist [v];
	}
    }

  return res;
}

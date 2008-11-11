#include "dbm.h"

#include <assert.h>
#include <stdlib.h>

dbm_t * 
dbm_alloc (unsigned int mindim, unsigned int maxdim)
{
  dbm_t * dbm;
  
  assert (mindim < maxdim);

  dbm = (dbm_t*)malloc (sizeof (dbm_t));
  if (dbm == NULL) return NULL;

  dbm->mindim = mindim;
  dbm->maxdim = maxdim;
  dbm->width = maxdim - mindim + 1;

  dbm->data = (struct dbm_value*) 
    malloc (sizeof (struct dbm_value) * (dbm->width) * (dbm->width));
  
  if (dbm->data == NULL)
    {
      free (dbm);
      return NULL;
    }
  return dbm;
}

void 
dbm_init (dbm_t * dbm)
{
  dbm->unsat = 0;
  /* initially, DBM is closed since it has no entries */
  dbm->closed = 1;
  
  /* initialize */
  {
    int i;
    for (i = 0; i < (dbm->width * dbm->width); i++)
      dbm->data [i].inf = 1;
  }
}


dbm_t * 
dbm_create (unsigned int mindim, unsigned int maxdim)
{
  dbm_t * dbm;

  dbm = dbm_alloc (mindim, maxdim);
  dbm_init (dbm);

  return dbm;
}



void 
dbm_destory (dbm_t *dbm)
{
  if (dbm != NULL && dbm->data != NULL)
    free (dbm->data);
  dbm->data = NULL;

  if (dbm != NULL)
    free (dbm);
}

dbm_t *
dbm_dup (dbm_t *dbm)
{
  dbm_t * res;
  
  res = (dbm_t*) malloc (sizeof (dbm_t));
  if (res == NULL) return NULL;
  
  res->data = (struct dbm_value *) 
    malloc (sizeof (struct dbm_value *) * dbm->width * dbm->width);
  if (res->data == NULL)
    {
      free (res);
      return NULL;
    }
  
  
  res->mindim = dbm->mindim;
  res->maxdim = dbm->maxdim;
  res->width = dbm->width;
  res->unsat = dbm->unsat;
  res->closed = dbm->closed;
  
  {
    int i;
    for (i = 0; i < (dbm->width * dbm->width); i++)
      res->data [i] = dbm->data [i];
  }
  
  return res;
}

void
dbm_floyd_warshal (dbm_t * dbm)
{
  /* bailout quickly if possible */
  if (dbm->unsat || dbm->closed) return ;
  
  /* run the algorithm */
  {
    unsigned int i, j, k;
    
    for (k = 0; k < dbm->width; k++)
      for (i = 0; i < dbm->width; i++)
	for (j = 0; j < dbm->width; j++)
	  {
	    /* new distance from i to j */
	    int new_ij;
	    
	    /* distance from i to k is infinity */
	    if (dbm->data [i * dbm->width + k].inf)
	      continue;
	    /* distance from k to  j is infinity */
	    else if (dbm->data [k * dbm->width + j].inf)
	      continue;

	    new_ij = dbm->data [i * dbm->width + k].val + 
	      dbm->data [k * dbm->width + j].val;

	    /* check for negative weight cycles */
	    if (i == j && new_ij < 0)
	      {
		dbm->unsat = 1;
		break;
	      }
	    
	    if (dbm->data [i*dbm->width +j].inf ||
		new_ij < dbm->data [i*dbm->width + j].val)
	      {
		dbm->data [i*dbm->width + j].val = new_ij;
		dbm->data [i*dbm->width + j].inf = 0;
	      }
	    
	  }
  }

  dbm->closed = 1;
}

dbm_t * 
dbm_resize (dbm_t * dbm, unsigned int mindim, unsigned int maxdim)
{
  dbm_t * res;
  unsigned int prefix;
  unsigned int i, j;
  
  
  /* DBM invariant: dbm->mindim < dbm->maxdim */
  assert (mindim <= dbm->mindim);
  assert (dbm->maxdim <= maxdim);
  
  res = dbm_alloc (mindim, maxdim);
  if (res == NULL) return NULL; 
      
  
  /* copy dbm into res */
  prefix = dbm->mindim - mindim;
  for (i = 0; i < dbm->width; i++)
    for (j = 0; j < dbm->width; j++)
      {
	res->data [(prefix + i) * res->width + (prefix + j)] =
	  dbm->data [i * dbm->width + j];
      }

  /* initialize the rest of res */

  /* the prefix */
  for (i = 0; i < prefix; i++)
    for (j = 0; j < prefix; j++)
      res->data [i * res->width + j].inf = 1;
  
  /* the suffix */
  for (i = dbm->maxdim + 1; i < res->width; i++)
    for (j = dbm->maxdim + 1; j < res->width; j++)
      res->data [i * res->width + j].inf = 1;
  
  return res;
}


dbm_t * 
dbm_update_entry (dbm_t * dbm, int dim1, int dim2, int cst)
{
  dbm_t * res;
  

  assert (dim1 != dim2);

  /* if the dbm is unsat, don't bother adding anything */
  if (dbm->unsat) return dbm;
  

  /* check if we need to resize */
  if (dim1 < dbm->mindim || dim1 > dbm->maxdim ||
      dim2 < dbm->mindim || dim2 > dbm->maxdim)
    {
      unsigned int mindim;
      unsigned int maxdim;

      /* mindim = MIN (dbm->mindim, dim1, dim2) */
      mindim = dbm->mindim < dim1 ? dbm->mindim : dim1;
      mindim = mindim < dim2 ? mindim : dim2;
      
      /* maxdim = MAX (dbm->mindim, dim1, dim2) */
      maxdim = dbm->maxdim > dim1 ? dbm->maxdim : dim1;
      maxdim = maxdim > dim2 ? maxdim : dim2;
      
      res = dbm_resize (dbm, mindim, maxdim);
    }

  /* check if we need to update at all */
  else  if (!dbm->data [dim1 * dbm->width + dim2].inf &&
	    dbm->data [dim1 * dbm->width + dim2].val <= cst) 
    return dbm;

  /* just a local update */
  else
    res = dbm_dup (dbm);
  

  assert (res->mindim <= dim1 && dim1 <= res->maxdim &&
	  res->mindim <= dim2 && dim2 <= res->maxdim);
  
  res->data [dim1 * dbm->width + dim2].inf = 0;
  res->data [dim1 * dbm->width + dim2].val = cst;

  /* adding a new constraint opens the DBM */
  res->closed = 0;
  /* since DBM is not closed, don't know it's SAT status */
  res->unsat = 0;

  return res;
  
}




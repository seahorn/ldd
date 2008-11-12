/* A library to manipulate and solve Difference Bound Matricies (DBMs) */
#ifndef _DBM__H_
#define _DBM__H_

#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif



/* DBM entries are integers */

struct dbm_value
{
  int val;
  /* Set if value represents infinity */
  unsigned inf:1;
};


  /* The DBM */
typedef struct dbm
{
  /* the entries */
  struct dbm_value *data;
  /* the smallest dimension */
  unsigned int mindim;
  /* the largest dimension */
  unsigned int maxdim;
  /* the width == maxdim - mindim + 1 */
  unsigned int width;
  
  /* Set if the DBM is unsatisfiable */
  unsigned unsat:1;
  /* Set if the DBM is closed */
  unsigned closed:1;
  
} dbm_t;
  

/* Access cel (i,j) of the DBM */
#define DBM_CEL(dbm,i,j) (dbm)->data[(i)*(dbm)->width + (j)]

/* Access dimension (i, j) of the DBM */
#define DBM_DIM(dbm,i,j) DBM_CEL(dbm, (i)-(dbm)->mindim, (j)-(dbm)->mindim)


  

/* Applyes Floyd Warshal algorithm to close the DBM.  As a side effect
 * dbm->closed is set to 1 and dbm->unsat may be set to 1.
 */
void  dbm_floyd_warshal (dbm_t* dbm);

/**
 * Updates entry DBM[dim1,dim2] to cst. If cst is less than the
 * current value, a new update DBM is returned. If cst is greater or
 * equal than the current value, the input dbm is returned.
 */
dbm_t * dbm_update_entry (dbm_t* dbm, int dim1, int dim2, int cst);

/**
 * Updates an entry in a DBM and computes its closures.  Required:
 * dbm->closed == 1 This is more efficient version of dbm_update_entry
 * followed by a DBM closure such as dbm_floyd_warshal.
  */
dbm_t * dbm_update_entry_close (dbm_t* dbm, int dim1, int dim2, int cst);


/**
 * Creates a duplicate copy.
 */
dbm_t * dbm_dup (dbm_t * dbm);

/** Deallocates memory */
void dbm_destory (dbm_t* dbm);

/** Creates an empty dbm */
dbm_t *dbm_create (unsigned int mindim, unsigned int maxdim);

/** Creates a DBM and initializes it with the constraint dim1 - dim2 <= cst */
dbm_t * dbm_create_init (unsigned int dim1, unsigned int dim2, int cst);


/*** Low level functions. Use with care */

/* Allocates memory for a DBM */
dbm_t *dbm_alloc (unsigned int mindim, unsigned int maxdim);
/* Initializes a DBM */
void dbm_init (dbm_t *dbm);

/* Resizes the DBM to accomodate new mindim and maxdim */
dbm_t* dbm_resize(dbm_t *dbm, unsigned int mindim, unsigned int maxdim);

  /* Outputs debugging information */
void dbm_debug_dump (FILE* out, dbm_t *dbm);

/** dbm_to_tdd */

#ifdef __cplusplus
}
#endif


#endif 

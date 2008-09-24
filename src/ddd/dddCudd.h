#ifndef _DDDCUDD_H_
#define _DDDCUDD_H_
#include "cudd.h"

#include <limits.h>

/*--------------------------------------------------------------------------*/
/* Macro declarations                                                       */
/*--------------------------------------------------------------------------*/

#define PINF        INT_MAX
#define NINF        INT_MIN
#define IS_PINF(X)  ((X) == PINF)
#define IS_NINF(X)  ((X) == NINF)
#define IS_LEQ(X,Y) ((X) <= (Y))
#define NUM_MIN(X,Y)   ((X) <= (Y) ? (X) : (Y))
#define NUM_MAX(X,Y)   ((X) <= (Y) ? (Y) : (X))


/*--------------------------------------------------------------------------*/
/* Type declarations                                                        */
/*--------------------------------------------------------------------------*/

/**
 * "variable" is always used to refer to BDD variables.  
 * "dimension" is used to refer to variables appearing in the constarint.
 */

typedef struct vinfo 
{
  /* first dimension */
  int fst; 
  /* second dimension */
  int snd;
  /* constant */
  int cst;
  
  /* pointer to DD node representing the constraint (fst-snd<=cst) */
  DdNode * node;

  /** pointers to next and prev. entries in a linked list */
  struct vinfo * next;
  struct vinfo * prev;
  
} vinfo;

typedef vinfo * pvinfo;

typedef struct dddManager dddManager;

/*--------------------------------------------------------------------------*/
/* Function declarations                                                    */
/*--------------------------------------------------------------------------*/
extern dddManager *dddCudd_Init(DdManager *, int);

extern DdNode *dddCons (dddManager *, int, int, int);

extern DdNode *dddOr (dddManager *, DdNode*, DdNode*);
extern DdNode *dddAnd (dddManager *, DdNode*, DdNode*);
extern DdNode *dddXor (dddManager *, DdNode*, DdNode*);
extern DdNode *dddIte (dddManager *, DdNode*, DdNode*, DdNode*);

extern DdNode *dddRelax (dddManager *, DdNode *, int, int, int, int, int[]);
extern DdNode *dddPropCons (dddManager *, DdNode *, int, int, int, int);
extern DdNode *dddExistAbstract (dddManager *, DdNode *, int[]);
extern DdNode *dddUnivAbstract (dddManager *, DdNode *, int[]);

/**AutomaticEnd***************************************************************/
#endif

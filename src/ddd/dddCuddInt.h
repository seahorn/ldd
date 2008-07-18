#ifndef _DDDCUDDINT_H_
#define _DDDCUDDINT_H_

#define CUDD_MAIN
#include "cuddInt.h"
#undef CUDD_MAIN

#include "dddCudd.h"

#define DD_DDD_ITE_TAG 0x8a

/*--------------------------------------------------------------------------*/
/* Macro declarations                                                       */
/*--------------------------------------------------------------------------*/

#define IS_PINF(X)  ((X) == INT_MAX)
#define IS_NINF(X)  ((X) == INT_MIN)
#define IS_LEQ(X,Y) ((X) <= (Y))
#define NUM_MIN(X,Y)   ((X) <= (Y) ? (X) : (Y))
#define NUM_MAX(X,Y)   ((X) <= (Y) ? (Y) : (X))
/*--------------------------------------------------------------------------*/
/* Type declarations                                                        */
/*--------------------------------------------------------------------------*/

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


struct dddManager {
  DdManager *cudd; // a regular DdManager
  void *gen; // useful pointer for various things
  
  /* a map from DD variable index to var info */
  pvinfo * ddVars;
  /** size of the ddVars array */
  int varsSize;
  
  
  /* a map from dimensions to var info */
  pvinfo * dims;
  
  /** size of the dims array */
  int dimSize;
  
  
  
};


/* 
 * Returns vinfo of a node 
 */
#define DDD_VAR_INFO(ddd,index) ((ddd)->ddVars [(index)])
#define DDD_SAME_DIM(node1,node2) (((node1)->fst == (node2)->fst) &&	\
				   ((node1)->snd == (node2)->snd))


/**AutomaticStart************************************************************/

/*--------------------------------------------------------------------------*/
/* Function prototypes                                                      */
/*--------------------------------------------------------------------------*/

extern dddManager * dddCudd_Init (DdManager*, int);
extern DdNode * dddCons(dddManager *, int, int, int);

extern DdNode * dddUniqueInter(dddManager *,int,int,int,DdNode*,DdNode*);


/**AutomaticEnd**************************************************************/
#endif

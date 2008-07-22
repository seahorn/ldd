#ifndef _DDDCUDDINT_H_
#define _DDDCUDDINT_H_

#define CUDD_MAIN
#include "cuddInt.h"
#undef CUDD_MAIN

#include "dddCudd.h"

/*--------------------------------------------------------------------------*/
/* Macro declarations                                                       */
/*--------------------------------------------------------------------------*/

#define DD_DDD_ITE_TAG 0x8a

/*--------------------------------------------------------------------------*/
/* Type declarations                                                        */
/*--------------------------------------------------------------------------*/
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


extern DdNode *dddUniqueInter(dddManager *,int,int,int, DdNode *, DdNode *);

extern DdNode *dddAndRecur (dddManager*, DdNode*, DdNode*);
extern DdNode *dddXorRecur (dddManager*, DdNode*, DdNode*);
extern DdNode *dddIteRecur (dddManager*, DdNode*, DdNode*, DdNode*);

extern DdNode * dddPropConsRecur (dddManager *, DdNode *, 
				  int, int, int, int, DdHashTable*);
extern DdNode *dddExistAbstractRecur (dddManager *, DdNode *, int*, 
				      DdHashTable*);
extern DdNode *dddRelaxRecur (dddManager *, DdNode *, 
			      int, int, int, int, int*, DdHashTable*);


/**AutomaticEnd**************************************************************/
#endif

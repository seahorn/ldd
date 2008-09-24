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
  
  
  /*
   * A map from dimensions to var info. Each entry of the array is a
   * linked list of var infos.  A constraint of the form (x - y <= c)
   * is stored in a linked list at dims[x]. The linked list is ordered
   * using the pair (y, c) as the key.
   */
  pvinfo * dims;
  
  /** size of the dims array */
  int dimSize;  
};


/* A matrix with m rows and n columns*/
typedef struct matrix
{
  int m;
  int n;
  int * data;
} matrix;

typedef matrix * pmatrix;

/* get M[I,J] */
#define M_GET(M,I,J) ((M)->data[I*(M)->n+(J)])
/* set M[I,J] to V */
#define M_SET(M,I,J,V) ((M)->data[I*(M)->n+(J)] = V)


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


/* matrix functions */
extern pmatrix matrix_create(int,int);
extern pmatrix matrix_create_square(int);
extern void matrix_destroy(pmatrix);
extern void matrix_fill(pmatrix,int);
extern pmatrix matrix_dup(pmatrix);
extern void matrix_floyd_warshall(pmatrix);
extern int ddd_is_sat(pmatrix);


/**AutomaticEnd**************************************************************/
#endif

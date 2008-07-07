#ifndef _DDDCUDD_H_
#define _DDDCUDD_H_
#include "cudd.h"

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/
typedef struct dddManager dddManager;

extern DdNode *dddOr (dddManager *, DdNode*, DdNode*);
extern DdNode *dddAnd (dddManager *, DdNode*, DdNode*);
extern DdNode *dddXor (dddManager *, DdNode*, DdNode*);
extern DdNode *dddIte (dddManager *, DdNode*, DdNode*, DdNode*);

/**AutomaticEnd***************************************************************/
#endif

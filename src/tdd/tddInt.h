#ifndef _TDDINT__H_
#define _TDDINT__H_

/**
 * Internal header file. To be used by the tdd library and its extensions.
 */

#include "tdd.h"
#include "cuddInt.h"

/** Macros for internal-only use */

#define DD_LDD_ITE_TAG 0x8a

#define CUDD ldd->cudd
#define THEORY ldd->theory

/**
 * tdd manager 
 */
struct LddManager
{
  /** underlying cudd manager */
  DdManager * cudd;

  /** a map from DD variables to corresponding linear constraints */
  lincons_t* ddVars;

  /** size of ddVars array */
  size_t varsSize;

  /** be like a BDD */
  bool be_bddlike;

  theory_t* theory;

  /** default implementation of existential quantification of a single
      variable */
  LddNode* (*existsAbstract)(LddManager*,LddNode*,int);
};

/**
 * Extracts a constraint corresponding to a given index
 */
#define lddC(ldd,index) ((index)>=ldd->varsSize?NULL:(ldd)->ddVars[(index)])


LddNode* lddUniqueInter (LddManager *m, unsigned int idx, 
			    LddNode *n1, LddNode* n2);

LddNode* lddAndRecur (LddManager*, LddNode*, LddNode*);
LddNode* lddXorRecur (LddManager*, LddNode*, LddNode*);
LddNode* lddIteRecur (LddManager*, LddNode*, LddNode*, LddNode*);
LddNode* lddExistsAbstractFMRecur (LddManager*, LddNode*, int, 
				   DdLocalCache*);
LddNode * lddResolveElimInter (LddManager * tdd, LddNode * f, 
				   linterm_t t, lincons_t cons, int var);
LddNode* lddResolveElimRecur (LddManager*, LddNode*, 
				  linterm_t,lincons_t, lincons_t, int);

LddNode* lddResolveRecur(LddManager*, LddNode*, linterm_t, lincons_t, lincons_t, int, DdHashTable*);

LddNode* lddExistAbstractPATRecur (LddManager*, LddNode*, bool*, 
				   qelim_context_t *,
				   DdHashTable*);

LddNode* lddSatReduceRecur (LddManager*, LddNode*, 
				qelim_context_t*, int);
bool lddIsSatRecur (LddManager*, LddNode*, 
				qelim_context_t*);
LddNode* lddBddExistAbstractRecur (LddManager*, LddNode*, LddNode*);
LddNode* lddExistsAbstractSFMRecur (LddManager*, LddNode*, int, 
				    DdLocalCache*);

void lddDebugPrintMtr (MtrNode*);
int lddFixMtrTree (DdManager*, const char *, void*);

LddNode* lddBoxExtrapolateRecur (LddManager*, LddNode*, LddNode*);
LddNode* lddBoxWidenRecur (LddManager*, LddNode*, LddNode*);
LddNode* lddTermReplaceRecur (LddManager*, LddNode*, 
				  linterm_t, linterm_t, 
				  constant_t, 
				  constant_t, constant_t, 
				  DdHashTable*);
LddNode* lddTermMinmaxApproxRecur (LddManager*, LddNode*);
LddNode* lddTermConstrainRecur (LddManager*, LddNode*, 
				    linterm_t, linterm_t, constant_t,
				    DdLocalCache*);
LddNodeset* lddNodesetUnionRecur(LddManager*, LddNodeset*, LddNodeset*);

int lddIsValidNodeset (LddManager*, LddNodeset*);

LddNode *lddSubstNinfForVarRecur (LddManager*, LddNode*, int, DdHashTable*);


#endif

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
};

/**
 * Extracts a constraint corresponding to a given index
 */
#define tddC(tdd,index) ((index)>=tdd->varsSize?NULL:(tdd)->ddVars[(index)])
#define lddC(ldd,index) ((index)>=ldd->varsSize?NULL:(ldd)->ddVars[(index)])


LddNode* Ldd_unique_inter (LddManager *m, unsigned int idx, 
			    LddNode *n1, LddNode* n2);

LddNode* Ldd_and_recur (LddManager*, LddNode*, LddNode*);
LddNode* Ldd_xor_recur (LddManager*, LddNode*, LddNode*);
LddNode* Ldd_ite_recur (LddManager*, LddNode*, LddNode*, LddNode*);
LddNode* Ldd_exist_abstract_recur (LddManager*, LddNode*, int, 
				    DdHashTable*);
LddNode * Ldd_resolve_elim_inter (LddManager * tdd, LddNode * f, 
				   linterm_t t, lincons_t cons, int var);
LddNode* Ldd_resolve_elim_recur (LddManager*, LddNode*, 
				  linterm_t,lincons_t, lincons_t, int);

LddNode* Ldd_resolve_recur(LddManager*, LddNode*, linterm_t, lincons_t, lincons_t, int, DdHashTable*);

LddNode* Ldd_exist_abstract_v2_recur (LddManager*, LddNode*, bool*, 
				       qelim_context_t *,
				       DdHashTable*);

LddNode* Ldd_sat_reduce_recur (LddManager*, LddNode*, 
				qelim_context_t*, int);
bool Ldd_is_sat_recur (LddManager*, LddNode*, 
				qelim_context_t*);
LddNode* Ldd_bdd_exist_abstract_recur (LddManager*, LddNode*, LddNode*);
LddNode* Ldd_exist_abstract_v3_recur (LddManager*, LddNode*, int, 
				       DdHashTable*);

void Ldd_debug_print_mtr (MtrNode*);
int Ldd_fix_mtr_tree (DdManager*, const char *, void*);

LddNode* Ldd_box_extrapolate_recur (LddManager*, LddNode*, LddNode*);
LddNode* Ldd_term_replace_recur (LddManager*, LddNode*, 
				  linterm_t, linterm_t, 
				  constant_t, 
				  constant_t, constant_t, 
				  DdHashTable*);
LddNode* Ldd_term_minmax_approx_recur (LddManager*, LddNode*);
LddNode* Ldd_term_constrain_recur (LddManager*, LddNode*, 
				    linterm_t, linterm_t, constant_t,
				    DdHashTable*);
LddNodeset* LddNodeset_union_recur(LddManager*, LddNodeset*, LddNodeset*);

int Ldd_is_valid_nodeset (LddManager*, LddNodeset*);

LddNode *lddSubstNinfForVarRecur (LddManager*, LddNode*, int, DdHashTable*);


#endif

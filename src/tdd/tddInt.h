#ifndef _TDDINT__H_
#define _TDDINT__H_

/**
 * Internal header file. To be used by the tdd library and its extensions.
 */

#include "tdd.h"
#include "cuddInt.h"

/** Macros for internal-only use */

#define DD_TDD_ITE_TAG 0x8a

#define CUDD tdd->cudd
#define THEORY tdd->theory

/**
 * tdd manager 
 */
struct tdd_manager
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


tdd_node* tdd_unique_inter (tdd_manager *m, unsigned int idx, 
			    tdd_node *n1, tdd_node* n2);

tdd_node* tdd_and_recur (tdd_manager*, tdd_node*, tdd_node*);
tdd_node* tdd_xor_recur (tdd_manager*, tdd_node*, tdd_node*);
tdd_node* tdd_ite_recur (tdd_manager*, tdd_node*, tdd_node*, tdd_node*);
tdd_node* tdd_exist_abstract_recur (tdd_manager*, tdd_node*, int, 
				    DdHashTable*);
tdd_node * tdd_resolve_elim_inter (tdd_manager * tdd, tdd_node * f, 
				   linterm_t t, lincons_t cons, int var);
tdd_node* tdd_resolve_elim_recur (tdd_manager*, tdd_node*, 
				  linterm_t,lincons_t, lincons_t, int);

tdd_node* tdd_resolve_recur(tdd_manager*, tdd_node*, linterm_t, lincons_t, lincons_t, int, DdHashTable*);

tdd_node* tdd_exist_abstract_v2_recur (tdd_manager*, tdd_node*, bool*, 
				       qelim_context_t *,
				       DdHashTable*);

tdd_node* tdd_sat_reduce_recur (tdd_manager*, tdd_node*, 
				qelim_context_t*, int);
bool tdd_is_sat_recur (tdd_manager*, tdd_node*, 
				qelim_context_t*);
tdd_node* tdd_bdd_exist_abstract_recur (tdd_manager*, tdd_node*, tdd_node*);
tdd_node* tdd_exist_abstract_v3_recur (tdd_manager*, tdd_node*, int, 
				       DdHashTable*);

void tdd_debug_print_mtr (MtrNode*);
int tdd_fix_mtr_tree (DdManager*, const char *, void*);

tdd_node* tdd_box_extrapolate_recur (tdd_manager*, tdd_node*, tdd_node*);
tdd_node* tdd_term_replace_recur (tdd_manager*, tdd_node*, 
				  linterm_t, linterm_t, 
				  constant_t, 
				  constant_t, constant_t, 
				  DdHashTable*);
tdd_node* tdd_term_minmax_approx_recur (tdd_manager*, tdd_node*);
tdd_node* tdd_term_constrain_recur (tdd_manager*, tdd_node*, 
				    linterm_t, linterm_t, constant_t,
				    DdHashTable*);
tdd_nodeset* tdd_nodeset_union_recur(tdd_manager*, tdd_nodeset*, tdd_nodeset*);

#endif

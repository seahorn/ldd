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

  theory_t* theory;
};


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

#endif

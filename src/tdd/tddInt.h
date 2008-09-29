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




#endif

/**********************************************************************
 * Private header file. Contains things that are not visible outside
 * of this module
 *********************************************************************/

#ifndef __BOX_INT_H
#define __BOX_INT_H


#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <float.h>
#include <string.h>
#include <assert.h>
#include <gmp.h>
#include "tdd-tvpi.h"
#include "tddInt.h"

#ifdef __cplusplus
extern "C" {
#endif

  typedef mpz_t* box_cst_t;
  
  
  /* represents a constraint  x <= cst */
  struct box_cons
  {
    /* if true, var is negated */
    bool negative;
    /* the variable */
    int var;
    /* the constant */
    box_cst_t cst;
  };
  
  typedef struct box_cons*  box_cons_t;

  /* Don't distinguish between terms and constraints */
  typedef box_cons_t box_term_t;
  
  /* a link list element. Used to map constraints to nodes*/
  typedef struct box_list_node
  {
    box_cons_t cons;
    tdd_node * dd;
    struct box_list_node *next;
    struct box_list_node *prev;
  } box_list_node_t;
    
  typedef struct box_theory
  {
    /* the base interface */
    theory_t base;
    /* # of variables */
    size_t var_num;
    /* maps each variable to the list of constraints it appears in */
    box_list_node_t **map;
  } box_theory_t;
  

  box_cst_t new_cst();
  box_cons_t new_cons ();
  box_term_t new_term ();
  box_cst_t box_create_si_cst(int);
  box_cst_t box_negate_cst (box_cst_t);
  box_cst_t box_dup_cst (box_cst_t);
  box_cst_t box_add_cst (box_cst_t,box_cst_t);
  box_cst_t box_mul_cst (box_cst_t,box_cst_t);
  int box_sgn_cst (box_cst_t);
  void box_destroy_cst (box_cst_t);
  void box_print_cst (FILE*, box_cst_t);
  
  box_term_t box_create_linterm (int*, size_t);
  bool box_term_equlas (box_term_t, box_term_t);
  bool box_term_has_var (box_term_t, int);
  bool box_term_has_vars (box_term_t t, int*);
  int box_pick_var (box_term_t,bool*);
  box_term_t box_dup_term (box_term_t);
  box_term_t box_negate_term (box_term_t);
  void box_destroy_term (box_term_t);
  void box_print_term (FILE*, box_term_t);

  box_cons_t box_create_cons (box_term_t,bool,box_cst_t);
  bool box_is_strict (box_cons_t);
  box_term_t box_get_term (box_cons_t);
  box_cst_t box_get_cst (box_cons_t);
  box_cons_t box_dup_cons (box_cons_t);
  box_cons_t box_negate_cons (box_cons_t);
  bool box_is_neg_cons (box_cons_t);
  bool box_is_stronger_cons (box_cons_t,box_cons_t);
  box_cons_t box_resolve_cons (box_cons_t,box_cons_t,int);
  void box_destroy_cons (box_cons_t);
  
  void box_print_cons (FILE*, box_cons_t);
  

  size_t box_num_of_vars (box_theory_t *);
  
  bool always_false_cst (box_cst_t k);
  
  
  

#ifdef __cplusplus
}
#endif


#endif

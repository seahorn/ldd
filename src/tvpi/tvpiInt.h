/**********************************************************************
 * Private header file. Contains things that are not visible outside
 * of this module
 *********************************************************************/

#ifndef __TVPI_INT_H
#define __TVPI_INT_H


#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <float.h>
#include <string.h>
#include <assert.h>
#include <gmp.h>
#include "tddInt.h"

#ifdef __cplusplus
extern "C" {
#endif

  typedef mpq_t* tvpi_cst_t;

  /* type of the comparison operator in a constraint */
  typedef enum {LT, LEQ} op_t;    
  
  
  /* represents a constraint  var[0] + coeff*var[1] <= cst */
  struct tvpi_cons
  {
    /* sign of the constraint, i.e., the sign of the coefficient of
       var[0]. <0 for negative, >0 for positive. Must not be =0. */
    int sgn;
    
    /* Comparison operator: strict (LT) or non-strict (LEQ) */
    op_t op;
    /* the variables */
    int var[2];
    /* the coefficient of var[1] */
    tvpi_cst_t coeff;
    /* the constant */
    tvpi_cst_t cst;

    /* The coefficient of var[0]. If fst_coeff != NULL then sgn is ignored.
     * A constraint is normalized iff fst_coeff == NULL and sgn > 0
     */
    tvpi_cst_t fst_coeff;
  };
  
  /**
   * True if X is a legal variable identifier 
   */
#define IS_VAR(X) ((X)>=0)

  typedef struct tvpi_cons*  tvpi_cons_t;

  /* Don't distinguish between terms and constraints */
  typedef tvpi_cons_t tvpi_term_t;
  
  /* a link list element. Used to map constraints to nodes*/
  typedef struct tvpi_list_node
  {
    tvpi_cons_t cons;
    LddNode * dd;
    struct tvpi_list_node *next;
    struct tvpi_list_node *prev;
  } tvpi_list_node_t;
    
  typedef struct tvpi_theory
  {
    /* the base interface */
    theory_t base;
    /* size in # of variables */
    size_t size;
    /* maps a pair of variables to the list of constraints they appear in */
    tvpi_list_node_t ***map;
  } tvpi_theory_t;
  

  tvpi_cst_t tvpi_create_si_cst(int);
  tvpi_cst_t tvpi_negate_cst (tvpi_cst_t);
  tvpi_cst_t tvpi_dup_cst (tvpi_cst_t);
  tvpi_cst_t tvpi_add_cst (tvpi_cst_t,tvpi_cst_t);
  tvpi_cst_t tvpi_mul_cst (tvpi_cst_t,tvpi_cst_t);
  int tvpi_sgn_cst (tvpi_cst_t);
  void tvpi_destroy_cst (tvpi_cst_t);
  void tvpi_print_cst (FILE*, tvpi_cst_t);
  
  tvpi_term_t tvpi_create_linterm (int*, size_t);
  bool tvpi_term_equlas (tvpi_term_t, tvpi_term_t);
  bool tvpi_term_has_var (tvpi_term_t, int);
  bool tvpi_term_has_vars (tvpi_term_t t, int*);
  int tvpi_pick_var (tvpi_term_t,bool*);
  tvpi_term_t tvpi_dup_term (tvpi_term_t);
  tvpi_term_t tvpi_negate_term (tvpi_term_t);
  void tvpi_destroy_term (tvpi_term_t);
  void tvpi_print_term (FILE*, tvpi_term_t);

  tvpi_cons_t tvpi_create_cons (tvpi_term_t,bool,tvpi_cst_t);
  bool tvpi_is_strict (tvpi_cons_t);
  tvpi_term_t tvpi_get_term (tvpi_cons_t);
  tvpi_cst_t tvpi_get_cst (tvpi_cons_t);
  tvpi_cons_t tvpi_dup_cons (tvpi_cons_t);
  tvpi_cons_t tvpi_negate_cons (tvpi_cons_t);
  bool tvpi_is_neg_cons (tvpi_cons_t);
  bool tvpi_is_stronger_cons (tvpi_cons_t,tvpi_cons_t);
  tvpi_cons_t tvpi_resolve_cons (tvpi_cons_t,tvpi_cons_t,int);
  void tvpi_destroy_cons (tvpi_cons_t);
  
  void tvpi_print_cons (FILE*, tvpi_cons_t);
  

  size_t tvpi_num_of_vars (tvpi_theory_t *);
  
  
  

#ifdef __cplusplus
}
#endif


#endif

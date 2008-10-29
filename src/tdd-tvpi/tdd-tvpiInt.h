/**********************************************************************
 * This is a private header file to be included from tdd-tvpi.c. It
 * should not be visible to the outside. The public header file is
 * tdd-tvpi.h
 *********************************************************************/

#ifndef __TDD_TVPI_INT_H__
#define __TDD_TVPI_INT_H__

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <float.h>
#include <string.h>
#include <assert.h>
#include <gmp.h>
#include "tdd-tvpi.h"
#include "../tdd/tddInt.h"

/**********************************************************************
 * private data structures
 *********************************************************************/

/**********************************************************************
 * the types of TVPI theories -- we support rational and double
 *********************************************************************/
typedef enum tvpi_type { TVPI_RAT, TVPI_DBL } tvpi_type_t;

/**********************************************************************
 * a generic structure used to represent integer, rational, and double
 * constants.
 *********************************************************************/
typedef struct tvpi_cst 
{
  /* the type of the constant */
  tvpi_type_t type;

  /* the value of the constant */
  union 
  {
    mpq_t rat_val;
    double dbl_val;
  };
} tvpi_cst_t;

/**********************************************************************
 * a TVPI term is of the form (+-X +-Y) and consists of two
 * variables. they are maintained in a normalized form where X < Y.
 *********************************************************************/
typedef struct tvpi_term { 
  /* coefficients */
  mpq_t coeffs[2]; 
  /* variables */
  int vars[2];
} tvpi_term_t;
  
/**********************************************************************
 * a TVPI constraint is of the form T < C or T <= C where T is a term
 * and C is a constant
 *********************************************************************/
typedef struct tvpi_cons
{ 
  tvpi_term_t *term; //the term
  tvpi_cst_t *cst;   //the constant
  bool strict;       //whether the inequality is strict
} tvpi_cons_t;

/**********************************************************************
 * structure for a pair of a constraint and its correponding
 * tdd_node*. a sorted list of such structures, one per variable pair,
 * is used to maintain the map from constraints to tdd_nodes.
 *********************************************************************/
typedef struct tvpi_cons_node
{
  tvpi_cons_t *cons;
  tdd_node *node;
  struct tvpi_cons_node *next;
} tvpi_cons_node_t;

/**********************************************************************
 * this structure is used to return the result of the function that
 * checks if two terms can be resolved on a variable. if resolution is
 * possible, then "term" is the resulting term, "cst1" is index of the
 * coefficient of the second term by which the first term had to be
 * multiplied, and "cst2" is the index of the coefficient of the first
 * term by which the second term had to be multiplied. if no
 * resolution is possible, then "term" is NULL, and "cst1" and "cst2"
 * are undefined.
 *********************************************************************/
typedef struct tvpi_resolve {
  linterm_t term;
  int cst1,cst2;
} tvpi_resolve_t;

/**********************************************************************
 * the TVPI theory struct "extends" the theory struct
 *********************************************************************/
typedef struct tvpi_theory
{
  theory_t base;                     //the base theory
  tvpi_type_t type;                  //type of theory
  size_t var_num;                    //number of variables
  tvpi_cons_node_t ***cons_node_map; //map from constraints to DD
                                     //nodes, one per pair of variables
} tvpi_theory_t;

/**********************************************************************
 * private functions
 *********************************************************************/

constant_t tvpi_create_int_cst(int v);
constant_t tvpi_create_rat_cst(int n,int d);
constant_t tvpi_create_double_cst(double v);
void tvpi_negate_cst_inplace (tvpi_cst_t *c);
constant_t tvpi_negate_cst (constant_t c);
bool tvpi_cst_eq(constant_t c1,constant_t c2);
bool tvpi_cst_lt(constant_t c1,constant_t c2);
bool tvpi_cst_le(constant_t c1,constant_t c2);
constant_t tvpi_cst_add(constant_t c1,constant_t c2);
constant_t tvpi_cst_mul(constant_t c1,mpq_t c2);
bool tvpi_is_pinf_cst(constant_t c);
bool tvpi_is_ninf_cst(constant_t c);
void tvpi_destroy_cst(constant_t c);
linterm_t tvpi_create_linterm(int* coeffs, size_t n);
bool tvpi_term_equals(linterm_t t1, linterm_t t2);
bool tvpi_term_has_var (linterm_t t,int var);
bool tvpi_term_has_vars (linterm_t t,bool *vars);
size_t tvpi_num_of_vars(theory_t* self);
linterm_t _tvpi_create_linterm(mpq_t cf11,mpq_t cf12,int v1,
                               mpq_t cf21,mpq_t cf22,int v2);
void tvpi_print_cst(FILE *f,tvpi_cst_t *c);
void tvpi_print_term(FILE *f,tvpi_term_t *t);
void tvpi_print_cons(FILE *f,tvpi_cons_t *l);
tvpi_resolve_t _tvpi_terms_have_resolvent(tvpi_term_t *x1,tvpi_term_t *x2, int x);
int tvpi_terms_have_resolvent(linterm_t t1, linterm_t t2, int x);
void tvpi_negate_term_inplace(tvpi_term_t *t);
linterm_t tvpi_negate_term(linterm_t t);
int tvpi_pick_var (linterm_t t, int* vars);
void tvpi_destroy_term(linterm_t t);
void _tvpi_canonicalize_cons(tvpi_cons_t *l);
lincons_t _tvpi_create_int_cons(linterm_t t, bool s, constant_t k);
lincons_t tvpi_create_int_cons(linterm_t t, bool s, constant_t k);
lincons_t _tvpi_create_rat_cons(linterm_t t, bool s, constant_t k);
lincons_t tvpi_create_rat_cons(linterm_t t, bool s, constant_t k);
bool tvpi_is_strict(lincons_t l);
tvpi_term_t *tvpi_dup_term(tvpi_term_t *arg);
linterm_t tvpi_get_term(lincons_t l);
tvpi_cst_t *tvpi_dup_cst(tvpi_cst_t *arg);
constant_t tvpi_get_constant(lincons_t l);
lincons_t tvpi_negate_int_cons(lincons_t l);
lincons_t tvpi_negate_rat_cons(lincons_t l);
bool tvpi_is_negative_cons(lincons_t l);
bool tvpi_is_stronger_cons(lincons_t l1, lincons_t l2);
lincons_t tvpi_resolve_int_cons(lincons_t l1, lincons_t l2, int x);
lincons_t tvpi_resolve_rat_cons(lincons_t l1, lincons_t l2, int x);
void tvpi_destroy_lincons(lincons_t l);
lincons_t tvpi_dup_lincons(lincons_t l);
tdd_node *tvpi_get_node(tdd_manager* m,tvpi_cons_node_t *curr,
                       tvpi_cons_node_t *prev,tvpi_cons_t *c);
tdd_node* tvpi_to_tdd(tdd_manager* m, lincons_t l);
void tvpi_print_lincons(FILE *f,lincons_t l);
tvpi_theory_t *tvpi_create_theory_common(size_t vn);

#endif //__TDD_TVPI_INT_H__

/**********************************************************************
 * end of tdd-tvpiInt.h
 *********************************************************************/

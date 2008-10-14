/**********************************************************************
 * This is a private header file to be included from tdd-oct.c. It
 * should not be visible to the outside. The public header file is
 * tdd-oct.h
 *********************************************************************/

#ifndef __TDD_OCT_INT_H__
#define __TDD_OCT_INT_H__

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <float.h>
#include <string.h>
#include <assert.h>
#include "tdd-oct.h"
#include "../tdd/tddInt.h"

/**********************************************************************
 * private data structures
 *********************************************************************/

/**********************************************************************
 * a generic structure used to represent integer, rational, and double
 * constants.
 *********************************************************************/
typedef struct oct_cst 
{
  /* the type of the constant */
  oct_type_t type;

  /* the value of the constant */
  union 
  {
    int int_val;
    div_t rat_val;
    double dbl_val;
  };
} oct_cst_t;

/**********************************************************************
 * a OCT term is of the form (+-X +-Y) and consists of two
 * variables. they are maintained in a normalized form where X < Y.
 *********************************************************************/
typedef struct oct_term { int coeff1,var1,coeff2,var2; } oct_term_t;
  
/**********************************************************************
 * a OCT constraint is of the form T < C or T <= C where T is a term
 * and C is a constant
 *********************************************************************/
typedef struct oct_cons
{ 
  oct_term_t term; //the term
  oct_cst_t cst; //the constant
  bool strict; //whether the inequality is strict
} oct_cons_t;

/**********************************************************************
 * structure for a pair of a constraint and its correponding
 * tdd_node*. a sorted list of such structures, one per variable pair,
 * is used to maintain the map from constraints to tdd_nodes.
 *********************************************************************/
typedef struct oct_cons_node
{
  oct_cons_t cons;
  tdd_node *node;
  struct oct_cons_node *next;
} oct_cons_node_t;

/**********************************************************************
 * the OCT theory struct "extends" the theory struct
 *********************************************************************/
typedef struct oct_theory
{
  theory_t base;                    //the base theory
  oct_type_t type;                  //type of theory
  size_t var_num;                   //number of variables
  oct_cons_node_t ***cons_node_map; //map from constraints to DD
                                    //nodes, one per pair of variables
} oct_theory_t;

/**********************************************************************
 * private functions
 *********************************************************************/

constant_t oct_create_int_cst(int v);
constant_t oct_create_rat_cst(int n,int d);
constant_t oct_create_double_cst(double v);
void oct_negate_cst_inplace (oct_cst_t *c);
constant_t oct_negate_cst (constant_t c);
bool oct_cst_eq(constant_t c1,constant_t c2);
bool oct_cst_lt(constant_t c1,constant_t c2);
bool oct_cst_le(constant_t c1,constant_t c2);
constant_t oct_cst_add(constant_t c1,constant_t c2);
bool oct_is_pinf_cst(constant_t c);
bool oct_is_ninf_cst(constant_t c);
void oct_destroy_cst(constant_t c);
linterm_t oct_create_linterm(int* coeffs, size_t n);
bool oct_term_equals(linterm_t t1, linterm_t t2);
bool oct_term_has_var (linterm_t t,bool *vars);
size_t oct_num_of_vars(theory_t* self);
linterm_t _oct_create_linterm(int cf1,int v1,int cf2,int v2);
linterm_t _oct_terms_have_resolvent(linterm_t t1, linterm_t t2, int x);
int oct_terms_have_resolvent(linterm_t t1, linterm_t t2, int x);
void oct_negate_term_inplace(oct_term_t *t);
linterm_t oct_negate_term(linterm_t t);
int oct_pick_var (linterm_t t, int* vars);
void oct_destroy_term(linterm_t t);
lincons_t oct_create_int_cons(linterm_t t, bool s, constant_t k);
lincons_t oct_create_rat_cons(linterm_t t, bool s, constant_t k);
bool oct_is_strict(lincons_t l);
oct_term_t *dup_term(oct_term_t *arg);
linterm_t oct_get_term(lincons_t l);
oct_cst_t *dup_cst(oct_cst_t *arg);
constant_t oct_get_constant(lincons_t l);
lincons_t oct_negate_int_cons(lincons_t l);
lincons_t oct_negate_rat_cons(lincons_t l);
bool oct_is_negative_cons(lincons_t l);
bool oct_is_stronger_cons(lincons_t l1, lincons_t l2);
lincons_t oct_resolve_int_cons(lincons_t l1, lincons_t l2, int x);
lincons_t oct_resolve_rat_cons(lincons_t l1, lincons_t l2, int x);
void oct_destroy_lincons(lincons_t l);
lincons_t oct_dup_lincons(lincons_t l);
tdd_node *oct_get_node(tdd_manager* m,oct_cons_node_t *curr,
                       oct_cons_node_t *prev,oct_cons_t *c);
tdd_node* oct_to_tdd(tdd_manager* m, lincons_t l);
oct_theory_t *oct_create_theory_common(size_t vn);

#endif //__TDD_OCT_INT_H__

/**********************************************************************
 * end of tdd-octInt.h
 *********************************************************************/

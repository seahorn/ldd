/**********************************************************************
 * This is a private header file to be included from tdd-ddd.c. It
 * should not be visible to the outside. The public header file is
 * tdd-ddd.h
 *********************************************************************/

#ifndef __TDD_DDD_INT_H__
#define __TDD_DDD_INT_H__

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <float.h>
#include <string.h>
#include <assert.h>
#include "tdd-ddd.h"
#include "tddInt.h"

#ifdef __cplusplus
extern "C" {
#endif

/**********************************************************************
 * private data structures
 *********************************************************************/

/**********************************************************************
 * the types of DDD theories -- currently, we support integer,
 * rational and double
 *********************************************************************/
typedef enum ddd_type { DDD_INT, DDD_RAT, DDD_DBL } ddd_type_t;

/**********************************************************************
 * a generic structure used to represent integer, rational, and double
 * constants.
 *********************************************************************/
typedef struct ddd_cst 
{
  /* the type of the constant */
  ddd_type_t type;

  /* the value of the constant */
  union 
  {
    int int_val;
    div_t rat_val;
    double dbl_val;
  };
} ddd_cst_t;

/**********************************************************************
 * a DDD term is of the form X-Y and consists of two variables
 *********************************************************************/
typedef struct ddd_term { int var1,var2; } ddd_term_t;
  
/**********************************************************************
 * a DDD constraint is of the form T < C or T <= C where T is a term
 * and C is a constant
 *********************************************************************/
typedef struct ddd_cons
{ 
  ddd_term_t term; //the term
  ddd_cst_t cst; //the constant
  bool strict; //whether the inequality is strict
} ddd_cons_t;

/**********************************************************************
 * structure for a pair of a constraint and its correponding
 * tdd_node*. a sorted list of such structures, one per variable pair,
 * is used to maintain the map from constraints to tdd_nodes.
 *********************************************************************/
typedef struct ddd_cons_node
{
  ddd_cons_t cons;
  tdd_node *node;
  struct ddd_cons_node *next;
} ddd_cons_node_t;

/**********************************************************************
 * data structures for incremental quantifier elimination
 *********************************************************************/
typedef struct ddd_qelim_stack
{
  /* constraint being pushed onto the stack */
  ddd_cons_t *cons;
#ifdef DDD_QELIM_INC
  /* current DBM including cons */
  int *dbm;
  /* largest variable occurring in dbm. Undefined if dbm == NULL */
  int maxvar;
  /* true if dbm is unsat */
  bool unsat;
#endif
  /* next element in the stack */
  struct ddd_qelim_stack *next;
} ddd_qelim_stack_t;

typedef struct ddd_qelim_context
{
  /* the manager */
  tdd_manager *tdd;
  /* a bool-set representing all variables that are quantified out */
  bool *vars;
  /* the stack of current constraints */
  ddd_qelim_stack_t *stack;
} ddd_qelim_context_t;

/**********************************************************************
 * the DDD theory struct "extends" the theory struct
 *********************************************************************/
typedef struct ddd_theory
{
  theory_t base;                    //the base theory
  ddd_type_t type;                  //type of theory
  size_t var_num;                   //number of variables
  ddd_cons_node_t ***cons_node_map; //map from constraints to DD
                                    //nodes, one per pair of variables
} ddd_theory_t;

/**********************************************************************
 * private functions
 *********************************************************************/

constant_t ddd_create_int_cst(int v);
constant_t ddd_create_rat_cst(int n,int d);
constant_t ddd_create_double_cst(double v);
void ddd_negate_cst_inplace (ddd_cst_t *c);
constant_t ddd_negate_cst (constant_t c);
bool ddd_cst_eq(constant_t c1,constant_t c2);
bool ddd_cst_lt(constant_t c1,constant_t c2);
bool ddd_cst_le(constant_t c1,constant_t c2);
constant_t ddd_cst_add(constant_t c1,constant_t c2);
bool ddd_is_pinf_cst(constant_t c);
bool ddd_is_ninf_cst(constant_t c);
void ddd_destroy_cst(constant_t c);
linterm_t ddd_create_linterm(int* coeffs, size_t n);
bool ddd_term_equals(linterm_t t1, linterm_t t2);
bool ddd_term_has_var (linterm_t t, int var);
bool ddd_term_has_vars (linterm_t t, bool *vars);
size_t ddd_num_of_vars(theory_t* self);
linterm_t _ddd_create_linterm(int v1,int v2);
void ddd_print_cst(FILE *f,ddd_cst_t *c);
void ddd_print_term(FILE *f,ddd_term_t *t);
void ddd_print_cons(FILE *f,ddd_cons_t *l);
linterm_t _ddd_terms_have_resolvent(linterm_t t1, linterm_t t2, int x);
int ddd_terms_have_resolvent(linterm_t t1, linterm_t t2, int x);
void ddd_negate_term_inplace(ddd_term_t *t);
linterm_t ddd_negate_term(linterm_t t);
int ddd_pick_var (linterm_t t, int* vars);
void ddd_destroy_term(linterm_t t);
lincons_t _ddd_create_int_cons(linterm_t t, bool s, constant_t k);
lincons_t ddd_create_int_cons(linterm_t t, bool s, constant_t k);
lincons_t _ddd_create_rat_cons(linterm_t t, bool s, constant_t k);
lincons_t ddd_create_rat_cons(linterm_t t, bool s, constant_t k);
bool ddd_is_strict(lincons_t l);
ddd_term_t *ddd_dup_term(ddd_term_t *arg);
linterm_t ddd_get_term(lincons_t l);
ddd_cst_t *ddd_dup_cst(ddd_cst_t *arg);
constant_t ddd_get_constant(lincons_t l);
lincons_t ddd_negate_int_cons(lincons_t l);
lincons_t ddd_negate_rat_cons(lincons_t l);
bool ddd_is_negative_cons(lincons_t l);
bool ddd_is_stronger_cons(lincons_t l1, lincons_t l2);
lincons_t ddd_resolve_int_cons(lincons_t l1, lincons_t l2, int x);
lincons_t ddd_resolve_rat_cons(lincons_t l1, lincons_t l2, int x);
void ddd_destroy_lincons(lincons_t l);
lincons_t ddd_dup_lincons(lincons_t l);
tdd_node *ddd_get_node(tdd_manager* m,ddd_cons_node_t *curr,
                       ddd_cons_node_t *prev,ddd_cons_t *c);
tdd_node* ddd_to_tdd(tdd_manager* m, lincons_t l);
void ddd_print_lincons(FILE *f,lincons_t l);
void ddd_qelim_destroy_stack(ddd_qelim_stack_t *x);
qelim_context_t* ddd_qelim_init(tdd_manager *m,bool *vars);
void ddd_qelim_push(qelim_context_t* ctx, lincons_t l);
lincons_t ddd_qelim_pop(qelim_context_t* ctx);
tdd_node* ddd_qelim_solve(qelim_context_t* ctx);
void ddd_qelim_destroy_context(qelim_context_t* ctx);
ddd_theory_t *ddd_create_theory_common(size_t vn);

#ifdef __cplusplus
}
#endif

#endif //__TDD_DDD_INT_H__

/**********************************************************************
 * end of tdd-dddInt.h
 *********************************************************************/

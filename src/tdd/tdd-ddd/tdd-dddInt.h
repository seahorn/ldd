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

/**********************************************************************
 * private data structures
 *********************************************************************/

/**********************************************************************
 * the DDD theory struct "extends" the theory struct
 *********************************************************************/
typedef struct ddd_theory
{
  theory_t base;
  size_t var_num;
} ddd_theory_t;

/**********************************************************************
 * a generic structure used to represent integer, rational, and double
 * constants.
 *********************************************************************/
typedef enum ddd_cst_type { DDD_INT, DDD_RAT, DDD_DBL } ddd_cst_type_t;

typedef struct ddd_cst 
{
  /* the type of the constant */
  ddd_cst_type_t type;

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
 * private functions
 *********************************************************************/

constant_t ddd_create_int_cst(int v);
constant_t ddd_create_rat_cst(int n,int d);
constant_t ddd_create_double_cst(double v);
constant_t ddd_negate_cst (constant_t c);
bool ddd_cst_lt(constant_t c1,constant_t c2);
bool ddd_cst_le(constant_t c1,constant_t c2);
constant_t ddd_decr_cst(constant_t c);
bool ddd_is_pinf_cst(constant_t c);
bool ddd_is_ninf_cst(constant_t c);
void ddd_destroy_cst(constant_t c);
linterm_t ddd_create_linterm(int* coeffs, size_t n);
bool ddd_term_has_var (linterm_t t, int* var, size_t n);
int ddd_terms_have_resolvent(linterm_t t1, linterm_t t2, int x);
linterm_t ddd_negate_term(linterm_t t);
void ddd_destroy_term(linterm_t t);
lincons_t ddd_create_cons(linterm_t t, bool s, constant_t k);
bool ddd_is_strict(lincons_t l);
ddd_term_t *copy_term(ddd_term_t *arg);
linterm_t ddd_get_term(lincons_t l);
ddd_cst_t *copy_cst(ddd_cst_t *arg);
constant_t ddd_get_constant(lincons_t l);
lincons_t ddd_negate_cons(lincons_t l);
bool ddd_is_stronger_cons(lincons_t l1, lincons_t l2);

#endif //__TDD_DDD_INT_H__

/**********************************************************************
 * end of tdd-ddd.h
 *********************************************************************/

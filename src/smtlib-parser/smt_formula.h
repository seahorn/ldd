/** 
 * this header file contains data structures used to construct the AST
 * of an SMT formula via parsing. right now only quantified formulas
 * over boolean combinations of TVPI constraints are supported.
 */ 

#ifndef __SMT_FORMULA_H__
#define __SMT_FORMULA_H__

#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

/** an atomic SMT constraint */
typedef struct smt_cons
{
  int coeffs[2];
  char *vars[2];
  int strict;
  int bound;
} smt_cons_t;

/** top-level SMT formula type */
typedef enum smt_type {
  SMT_CONS,               //constraint
  SMT_AND,SMT_OR,SMT_NOT, //boolean
  SMT_EXISTS,SMT_FORALL   //quantification
} smt_type_t;

/** SMT formula */
typedef struct smt_formula
{
  /** the type of the formula */
  smt_type_t type;

  /** constraint -- this is NULL if type is not CONS */
  smt_cons_t *cons;

  /** NULL-terminated array of sub-formulas. if there are no
      sub-formulas, then subs = NULL.*/
  struct smt_formula **subs;

  /**
   * NULL-terminated array of variables quantified out -- if type is
   * not EXISTS or FORALL, then qVars is NULL.
  */
  char **qVars;
} smt_formula_t;

/** utility routines */
smt_formula_t *create_cons(int c1,char *v1,int c2,char *v2,int s,int b);
void destroy_cons(smt_cons_t *c);
void destroy_formula(smt_formula_t *f);
void print_cons(FILE *out,smt_cons_t *c);
void print_formula(FILE *out,smt_formula_t *f);

#ifdef __cplusplus
}
#endif

#endif //__SMT_FORMULA_H__

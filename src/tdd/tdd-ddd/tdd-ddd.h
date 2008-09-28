/**********************************************************************
 * This is a header file to be included from tdd-ddd.c.
 *********************************************************************/

#ifndef __TDD_DDD_H__
#define __TDD_DDD_H__

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <math.h>
#include <string.h>
#include "../theory.h"

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
  

#endif //__TDD_DDD_H__

/**********************************************************************
 * end of tdd-ddd.h
 *********************************************************************/

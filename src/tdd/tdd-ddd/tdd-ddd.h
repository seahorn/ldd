/**********************************************************************
 * This is a private header file to be included from tdd-ddd.c. It is
 * not meant to be visible externally.
 *********************************************************************/

#ifndef __TDD_DDD_H__
#define __TDD_DDD_H__

#include <stdio.h>
#include <stdlib.h>
#include "../theory.h"

/**********************************************************************
 * a generic structure used to represent integer, rational, and double
 * constants.
 *********************************************************************/
typedef enum ddd_const_type { DDD_INT, DDD_RAT, DDD_DBL } ddd_const_type_t;

typedef struct ddd_const 
{
  /* the type of the constant */
  ddd_const_type_t type;

  /* the value of the constant */
  union 
  {
    int int_val;
    div_t rat_val;
    double dbl_val;
  };
} ddd_const_t;

#endif //__TDD_DDD_H__

/**********************************************************************
 * end of tdd-ddd.h
 *********************************************************************/

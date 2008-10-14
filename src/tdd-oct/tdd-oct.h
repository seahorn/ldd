/**********************************************************************
 * This is a header file to be included from tdd-ddd.c.
 *********************************************************************/

#ifndef __TDD_DDD_H__
#define __TDD_DDD_H__

#include "../tdd/tdd.h"

/**********************************************************************
 * the types of DDD theories -- currently, we support integer,
 * rational and double
 *********************************************************************/
typedef enum ddd_type { DDD_INT, DDD_RAT, DDD_DBL } ddd_type_t;

/**********************************************************************
 * public functions -- for creating and destroying a DDD theory
 *********************************************************************/

theory_t *ddd_create_int_theory(size_t vn);
theory_t *ddd_create_rat_theory(size_t vn);
void ddd_destroy_theory(theory_t *t);

#endif //__TDD_DDD_H__

/**********************************************************************
 * end of tdd-ddd.h
 *********************************************************************/

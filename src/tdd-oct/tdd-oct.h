/**********************************************************************
 * This is a header file to be included from tdd-oct.c.
 *********************************************************************/

#ifndef __TDD_OCT_H__
#define __TDD_OCT_H__

#include "tdd.h"

#ifdef __cplusplus
extern "C" {
#endif

/**********************************************************************
 * public functions -- for creating and destroying a OCT theory
 *********************************************************************/

theory_t *oct_create_int_theory(size_t vn);
theory_t *oct_create_rat_theory(size_t vn);
void oct_destroy_theory(theory_t *t);

#ifdef __cplusplus
}
#endif

#endif //__TDD_OCT_H__

/**********************************************************************
 * end of tdd-oct.h
 *********************************************************************/

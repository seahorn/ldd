/**********************************************************************
 * This is a header file to be included from tdd-tvpi.c.
 *********************************************************************/

#ifndef __TDD_TVPI_H__
#define __TDD_TVPI_H__

#include "tdd.h"

#ifdef __cplusplus
extern "C" {
#endif

/**********************************************************************
 * public functions -- for creating and destroying a TVPI theory
 *********************************************************************/

theory_t *tvpi_create_int_theory(size_t vn);
theory_t *tvpi_create_rat_theory(size_t vn);
void tvpi_destroy_theory(theory_t *t);

#ifdef __cplusplus
}
#endif

#endif //__TDD_TVPI_H__

/**********************************************************************
 * end of tdd-tvpi.h
 *********************************************************************/

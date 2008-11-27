/** 
 * header file for a TDD based qelim solver.
 */ 

#ifndef __SMT_QELIM_SOLVER_H__
#define __SMT_QELIM_SOLVER_H__

#include <stdio.h>
#include "tdd.h"

#ifdef __cplusplus
extern "C" {
#endif

/** 
 * the main function accepts a filename and a tdd_manager as
 * input. the file should contain a SMT formula. it is parsed and then
 * solved. if the result is TRUE, return 1. if the result is FALSE,
 * return 0. otherwise return -1.
 */
int smt_qelim_solve(char *fileName,tdd_manager *tdd);

#ifdef __cplusplus
}
#endif

#endif //__SMT_QELIM_SOLVER_H__

/**********************************************************************
 * end of smt_qelim_solver.h
 *********************************************************************/

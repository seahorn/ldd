/**********************************************************************
 * The main file that provides the DDD theory.
 *********************************************************************/

#include "tdd-ddd.h"

/**********************************************************************
 * create an integer constant
 *********************************************************************/
constant_t ddd_create_int_cst(int v)
{
  int *res = (int*)malloc(sizeof(int));
  *res = v;
  return (constant_t)res;
}

/**********************************************************************
 * destroy an integer constant
 *********************************************************************/
void ddd_destroy_int_cst(constant_t c)
{
  free((int*)c);
}

/**********************************************************************
 * create a rational constant. we use the div_t datatype to store the
 * numerator and denominator.
 *********************************************************************/
constant_t ddd_create_rat_cst(int n,int d)
{
  div_t *res = (div_t*)malloc(sizeof(div_t));
  res->quot = n;
  res->rem = d;
  return (constant_t)res;
}

/**********************************************************************
 * destroy a rational constant
 *********************************************************************/
void ddd_destroy_rat_cst(constant_t c)
{
  free((div_t*)c);
}

/**********************************************************************
 * create a double constant
 *********************************************************************/
constant_t ddd_create_double_cst(double v)
{
  double *res = (double*)malloc(sizeof(double));
  *res = v;
  return (constant_t)res;
}

/**********************************************************************
 * destroy a double constant
 *********************************************************************/
void ddd_destroy_double_cst(constant_t c)
{
  free((double*)c);
}

/**********************************************************************
 * create a DDD theory
 *********************************************************************/
theory_t ddd_create_theory()
{
  theory_t res;
  res.create_int_cst = ddd_create_int_cst;
  res.destroy_int_cst = ddd_destroy_int_cst;
  res.create_rat_cst = ddd_create_rat_cst;
  res.destroy_rat_cst = ddd_destroy_rat_cst;
  res.create_double_cst = ddd_create_double_cst;
  res.destroy_double_cst = ddd_destroy_double_cst;
  return res;
}

/**********************************************************************
 * destroy a DDD theory
 *********************************************************************/
void ddd_destroy_theory(theory_t t)
{
}

/**********************************************************************
 * end of tdd-ddd.c
 *********************************************************************/

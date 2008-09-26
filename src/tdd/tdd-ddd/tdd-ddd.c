/**********************************************************************
 * The main file that provides the DDD theory.
 *********************************************************************/

#include "tdd-ddd.h"

/**********************************************************************
 * create an integer constant
 *********************************************************************/
constant_t ddd_create_int_cst(int v)
{
  ddd_const_t *res = (ddd_const_t*)malloc(sizeof(ddd_const_t));
  res->type = DDD_INT;
  res->int_val = v;
  return (constant_t)res;
}

/**********************************************************************
 * create a rational constant. we use the div_t datatype to store the
 * numerator and denominator.
 *********************************************************************/
constant_t ddd_create_rat_cst(int n,int d)
{
  ddd_const_t *res = (ddd_const_t*)malloc(sizeof(ddd_const_t));
  res->type = DDD_RAT;
  res->rat_val.quot = n;
  res->rat_val.rem = d;
  return (constant_t)res;
}

/**********************************************************************
 * create a double constant
 *********************************************************************/
constant_t ddd_create_double_cst(double v)
{
  ddd_const_t *res = (ddd_const_t*)malloc(sizeof(ddd_const_t));
  res->type = DDD_DBL;
  res->dbl_val = v;
  return (constant_t)res;
}

/**********************************************************************
 * destroy a constant
 *********************************************************************/
void ddd_destroy_cst(constant_t c)
{
  free((ddd_const_t*)c);
}

/**********************************************************************
 * return true if the argument is positive infinity
 *********************************************************************/
bool ddd_is_pinf_cst(constant_t c)
{
  ddd_const_t *x = (ddd_const_t*)c;
  switch(x->type)
    {
    case DDD_INT:
      return x->int_val == INT_MAX;
    case DDD_RAT:
      return (x->rat_val.rem == 0 && x->rat_val.quot > 0) || 
        (x->rat_val.quot == INT_MAX); 
    case DDD_DBL:
      return isinf(x->dbl_val) == 1;
    default:
      return 0;
    }
}

/**********************************************************************
 * return true if the argument is negative infinity
 *********************************************************************/
bool ddd_is_ninf_cst(constant_t c)
{
  ddd_const_t *x = (ddd_const_t*)c;
  switch(x->type)
    {
    case DDD_INT:
      return x->int_val == INT_MIN;
    case DDD_RAT:
      return (x->rat_val.rem == 0 && x->rat_val.quot < 0) || 
        (x->rat_val.quot == INT_MIN); 
    case DDD_DBL:
      return isinf(x->dbl_val) == -1;
    default:
      return 0;
    }
}

/**********************************************************************
 * create a DDD theory
 *********************************************************************/
theory_t ddd_create_theory()
{
  theory_t res;
  memset((void*)(&res),sizeof(theory_t),0);
  res.create_int_cst = ddd_create_int_cst;
  res.create_rat_cst = ddd_create_rat_cst;
  res.create_double_cst = ddd_create_double_cst;
  res.destroy_cst = ddd_destroy_cst;
  res.is_pinf_cst = ddd_is_pinf_cst;
  res.is_ninf_cst = ddd_is_ninf_cst;
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

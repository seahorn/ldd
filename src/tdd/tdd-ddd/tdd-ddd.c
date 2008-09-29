/**********************************************************************
 * The main file that provides the DDD theory.
 *********************************************************************/

#include "tdd-ddd.h"

/**********************************************************************
 * create an integer constant
 *********************************************************************/
constant_t ddd_create_int_cst(int v)
{
  ddd_cst_t *res = (ddd_cst_t*)malloc(sizeof(ddd_cst_t));
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
  ddd_cst_t *res = (ddd_cst_t*)malloc(sizeof(ddd_cst_t));
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
  ddd_cst_t *res = (ddd_cst_t*)malloc(sizeof(ddd_cst_t));
  res->type = DDD_DBL;
  res->dbl_val = v;
  return (constant_t)res;
}

/**********************************************************************
 * destroy a constant
 *********************************************************************/
void ddd_destroy_cst(constant_t c)
{
  free((ddd_cst_t*)c);
}

/**********************************************************************
 * return true if the argument is positive infinity
 *********************************************************************/
bool ddd_is_pinf_cst(constant_t c)
{
  ddd_cst_t *x = (ddd_cst_t*)c;
  switch(x->type)
    {
    case DDD_INT:
      return x->int_val == INT_MAX;
    case DDD_RAT:
      return (x->rat_val.quot == INT_MAX); 
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
  ddd_cst_t *x = (ddd_cst_t*)c;
  switch(x->type)
    {
    case DDD_INT:
      return x->int_val == INT_MIN;
    case DDD_RAT:
      return (x->rat_val.quot == INT_MIN); 
    case DDD_DBL:
      return isinf(x->dbl_val) == -1;
    default:
      return 0;
    }
}

/**********************************************************************
 * create a linear term. the first argument is an array of alternating
 * variables and coefficients. the second argument is the size of the
 * first argument.
 *********************************************************************/
linterm_t ddd_create_linterm(int* coeff_var, size_t n)
{
  /* for DDDs, the terms are of the form X-Y. hence n = 4, the first
     coefficient is +1 and the second coefficient is -1. */
  assert(n == 4 && coeff_var[0] == 1 && coeff_var[3] == -1);
  ddd_term_t *res = (ddd_term_t*)malloc(sizeof(ddd_term_t));
  res->var1 = coeff_var[1];
  res->var2 = coeff_var[3];
  return (linterm_t)res;
}

/**********************************************************************
 * Returns true if there exists a variable v in the array var whose
 * coefficient in t is non-zero.
 
 *  t is a term, var is an array of integers, and n is the size of
 *  var.
 *********************************************************************/
bool ddd_term_has_var (linterm_t t, int* var, size_t n)
{
  ddd_term_t *x = (ddd_term_t*)t;
  size_t i = 0;
  for(;i < n;++i) {
    if(x->var1 == var[i] || x->var2 == var[i]) return 1;
  }
  return 0;
}

/**********************************************************************
 * Returns >0 if t1 and t2 have a resolvent on variable x, 
 * Returns <0 if t1 and -t2 have a resolvent on variable x
 * Return 0 if t1 and t2 do not resolve.
 *********************************************************************/
int ddd_terms_have_resolvent(linterm_t t1, linterm_t t2, int x)
{
  ddd_term_t *x1 = (ddd_term_t*)t1;
  ddd_term_t *x2 = (ddd_term_t*)t2;
  if(x1->var2 == x2->var1 || x1->var1 == x2->var2) return 1;
  if(x1->var1 == x2->var1 || x1->var2 == x2->var2) return -1;
  return 0;
}

/**********************************************************************
 * return -1*t
 *********************************************************************/
linterm_t ddd_negate_term(linterm_t t)
{
  ddd_term_t *x = (ddd_term_t*)t;
  ddd_term_t *res = (ddd_term_t*)malloc(sizeof(ddd_term_t));
  res->var1 = x->var2;
  res->var2 = x->var1;
  return (linterm_t)res;
}

/**********************************************************************
 * reclaim resources allocated by t
 *********************************************************************/
void ddd_destroy_term(linterm_t t)
{
  free((ddd_term_t*)t);
}

/**********************************************************************
 * Creates a linear contraint t < k (if s is true) t<=k (if s is false)
 *********************************************************************/
lincons_t ddd_create_cons(linterm_t t, bool s, constant_t k)
{
  ddd_cons_t *res = (ddd_cons_t*)malloc(sizeof(ddd_cons_t));
  res->term = *((ddd_term_t*)t);
  res->cst = *((ddd_cst_t*)k);
  res->strict = s;
  return (lincons_t)res;
}

/**********************************************************************
 * Returns true if l is a strict constraint
 *********************************************************************/
bool ddd_is_strict(lincons_t l)
{
  ddd_cons_t *x = (ddd_cons_t*)l;
  return x->strict;
}

/**********************************************************************
 * copy a term. this is a private function.
 *********************************************************************/
ddd_term_t *copy_term(ddd_term_t *arg)
{
  ddd_term_t *res = (ddd_term_t*)malloc(sizeof(ddd_term_t));
  *res = *arg;
  return res;
}

/**********************************************************************
 * get the term corresponding to the argument constraint
 *********************************************************************/
linterm_t ddd_get_term(lincons_t l)
{
  ddd_cons_t *x = (ddd_cons_t*)l;  
  return (linterm_t)copy_term(&(x->term));
}

/**********************************************************************
 * copy a constant. this is a private function.
 *********************************************************************/
ddd_cst_t *copy_cst(ddd_cst_t *arg)
{
  ddd_cst_t *res = (ddd_cst_t*)malloc(sizeof(ddd_cst_t));
  *res = *arg;
  return res;
}

/**********************************************************************
 * get the constant corresponding to the argument constraint
 *********************************************************************/
constant_t ddd_get_constant(lincons_t l)
{
  ddd_cons_t *x = (ddd_cons_t*)l;  
  return (constant_t)copy_cst(&(x->cst));
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
  res.create_linterm = ddd_create_linterm;
  res.term_has_var = ddd_term_has_var;
  res.terms_have_resolvent = ddd_terms_have_resolvent;
  res.negate_term = ddd_negate_term;
  res.destroy_term = ddd_destroy_term;
  res.create_cons = ddd_create_cons;
  res.is_strict = ddd_is_strict;
  res.get_term = ddd_get_term;
  res.get_constant = ddd_get_constant;
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

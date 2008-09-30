/**********************************************************************
 * The main file that provides the DDD theory.
 *********************************************************************/

#include "tdd-dddInt.h"

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
 * Return -1*c
 *********************************************************************/
constant_t ddd_negate_cst (constant_t c)
{
  ddd_cst_t *x = (ddd_cst_t*)c;
  switch(x->type)
    {
    case DDD_INT:
      if(x->int_val == INT_MAX) return ddd_create_int_cst(INT_MIN);
      if(x->int_val == INT_MIN) return ddd_create_int_cst(INT_MAX);
      return ddd_create_int_cst(-(x->int_val));
    case DDD_RAT:
      if(x->rat_val.quot == INT_MAX) return ddd_create_rat_cst(INT_MIN,1);
      if(x->rat_val.quot == INT_MIN) return ddd_create_rat_cst(INT_MAX,1);
      return ddd_create_rat_cst(-(x->rat_val.quot),x->rat_val.rem); 
    case DDD_DBL:
      if(x->dbl_val == DBL_MAX) return ddd_create_double_cst(DBL_MIN);
      if(x->dbl_val == DBL_MIN) return ddd_create_double_cst(DBL_MAX);
      return ddd_create_double_cst(-(x->dbl_val));
    default:
      return 0;
    }
}

/**********************************************************************
 * Compares c1 and c2 for <
 * Returns true if c1 and c2 are of same type and c1 < c2
 * Returns false otherwise
 *********************************************************************/
bool ddd_cst_lt (constant_t c1,constant_t c2)
{
  ddd_cst_t *x1 = (ddd_cst_t*)c1;
  ddd_cst_t *x2 = (ddd_cst_t*)c2;

  if(x1->type != x2->type) return 0;

  switch(x1->type)
    {
    case DDD_INT:
      return (x1->int_val < x2->int_val);
    case DDD_RAT:
      if(ddd_is_pinf_cst(c1)) return 0;
      if(ddd_is_pinf_cst(c2)) return !ddd_is_pinf_cst(c1);
      if(ddd_is_ninf_cst(c1)) return !ddd_is_ninf_cst(c2);
      if(ddd_is_ninf_cst(c2)) return 0;
      return (x1->rat_val.quot * 1.0 / x1->rat_val.rem < x2->rat_val.quot * 1.0 / x2->rat_val.rem);
    case DDD_DBL:
      return (x1->dbl_val < x2->dbl_val);
    default:
      return 0;
    }
}

/**********************************************************************
 * Compares c1 and c2 for <=
 * Returns true if c1 and c2 are of same type and c1 <= c2
 * Returns false otherwise
 *********************************************************************/
bool ddd_cst_le (constant_t c1,constant_t c2)
{
  ddd_cst_t *x1 = (ddd_cst_t*)c1;
  ddd_cst_t *x2 = (ddd_cst_t*)c2;

  if(x1->type != x2->type) return 0;

  switch(x1->type)
    {
    case DDD_INT:
      return (x1->int_val <= x2->int_val);
    case DDD_RAT:
      if(ddd_is_pinf_cst(c1)) return ddd_is_pinf_cst(c2);
      if(ddd_is_pinf_cst(c2)) return 1;
      if(ddd_is_ninf_cst(c1)) return 1;
      if(ddd_is_ninf_cst(c2)) return ddd_is_ninf_cst(c1);
      return (x1->rat_val.quot * 1.0 / x1->rat_val.rem <= x2->rat_val.quot * 1.0 / x2->rat_val.rem);
    case DDD_DBL:
      return (x1->dbl_val <= x2->dbl_val);
    default:
      return 0;
    }
}

/**********************************************************************
 * if c is an integer, return c - 1, else return c
 *********************************************************************/
constant_t ddd_decr_cst(constant_t c)
{
  ddd_cst_t *x = (ddd_cst_t*)c;
  switch(x->type)
    {
    case DDD_INT:
      return ddd_is_pinf_cst(c) || ddd_is_ninf_cst(c) ? 
        (constant_t)copy_cst(x) : ddd_create_int_cst(x->int_val - 1);
    case DDD_RAT:
      return (constant_t)copy_cst(x);
    case DDD_DBL:
      return (constant_t)copy_cst(x);
    default:
      return 0;
    }
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
      return (x->dbl_val == DBL_MAX);
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
      return (x->dbl_val == DBL_MIN);
    default:
      return 0;
    }
}

/**********************************************************************
 * destroy a constant
 *********************************************************************/
void ddd_destroy_cst(constant_t c)
{
  free((ddd_cst_t*)c);
}

/**********************************************************************
 * Create a linear term: the first argument is an array of variable
 * coefficients. the second argument is the size of the array of
 * coefficients.
 *********************************************************************/
linterm_t ddd_create_linterm(int* coeffs, size_t n)
{
  ddd_term_t *res = (ddd_term_t*)malloc(sizeof(ddd_term_t));
  size_t i = 0;
  for(;i < n;++i) {
    if(coeffs[i] == 1) res->var1 = i;
    if(coeffs[i] == -1) res->var2 = i;
  }
  return (linterm_t)res;
}

/**********************************************************************
 * Returns true if t1 is the same term as t2
 *********************************************************************/
bool ddd_term_equals(linterm_t t1, linterm_t t2)
{
  ddd_term_t *x1 = (ddd_term_t*)t1;
  ddd_term_t *x2 = (ddd_term_t*)t2;
  return (x1->var1 == x2->var1 && x1->var2 == x2->var2);
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
 * Complements a linear constraint
 *********************************************************************/
lincons_t ddd_negate_cons(lincons_t l)
{
  linterm_t x = ddd_get_term(l);
  linterm_t y = ddd_negate_term(x);
  ddd_destroy_term(x);
  constant_t a = ddd_get_constant(l);
  constant_t b = ddd_negate_cst(a);
  ddd_destroy_cst(a);
  lincons_t res = ddd_create_cons(y,!ddd_is_strict(l),b);
  ddd_destroy_term(y);
  ddd_destroy_cst(b);
  return res;
}

/**********************************************************************
 * If is_stronger_cons(l1, l2) then l1 implies l2
 *********************************************************************/
bool ddd_is_stronger_cons(lincons_t l1, lincons_t l2)
{
  //get the terms and constants
  linterm_t x1 = ddd_get_term(l1);
  linterm_t x2 = ddd_get_term(l2);
  ddd_term_t *y1 = (ddd_term_t*)x1;
  ddd_term_t *y2 = (ddd_term_t*)x2;
  constant_t a1 = ddd_get_constant(l1);
  constant_t a2 = ddd_get_constant(l2);
  bool res = 0;

  //if the two terms are both of the form X-Y
  if(y1->var1 == y2->var1 && y1->var2 == y2->var2) {
    //if the terms are X-Y < C1 and X-Y <= C2 then C1 must be <= C2-1
    if(ddd_is_strict(l1) && !ddd_is_strict(l2)) {
      constant_t a3 = ddd_decr_cst(a2);
      res = ddd_cst_le(a1,a3);
      ddd_destroy_cst(a3);
    }
    //otherwise C1 must be <= C2
    else res = ddd_cst_le(a1,a2);
  }

  //deallocate
  ddd_destroy_term(x1);
  ddd_destroy_term(x2);
  ddd_destroy_cst(a1);
  ddd_destroy_cst(a2);

  //all done
  return res;
}

/**********************************************************************
 * create a DDD theory - the argument is the number of variables
 *********************************************************************/
theory_t *ddd_create_theory(size_t vn)
{
  ddd_theory_t *res = (ddd_theory_t*)malloc(sizeof(ddd_theory_t));
  memset((void*)(res),sizeof(ddd_theory_t),0);
  res->base.create_int_cst = ddd_create_int_cst;
  res->base.create_rat_cst = ddd_create_rat_cst;
  res->base.create_double_cst = ddd_create_double_cst;
  res->base.negate_cst = ddd_negate_cst;
  res->base.is_pinf_cst = ddd_is_pinf_cst;
  res->base.is_ninf_cst = ddd_is_ninf_cst;
  res->base.destroy_cst = ddd_destroy_cst;
  res->base.create_linterm = ddd_create_linterm;
  res->base.term_has_var = ddd_term_has_var;
  res->base.terms_have_resolvent = ddd_terms_have_resolvent;
  res->base.negate_term = ddd_negate_term;
  res->base.destroy_term = ddd_destroy_term;
  res->base.create_cons = ddd_create_cons;
  res->base.is_strict = ddd_is_strict;
  res->base.get_term = ddd_get_term;
  res->base.get_constant = ddd_get_constant;
  res->base.negate_cons = ddd_negate_cons;
  res->base.is_stronger_cons = ddd_is_stronger_cons;
  res->var_num = vn;
  return (theory_t*)res;
}

/**********************************************************************
 * destroy a DDD theory
 *********************************************************************/
void ddd_destroy_theory(theory_t *t)
{
  free((ddd_theory_t*)t);
}

/**********************************************************************
 * end of tdd-ddd.c
 *********************************************************************/

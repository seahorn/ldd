/**********************************************************************
 * The main file that provides the TVPI theory.
 *********************************************************************/

#include "tdd-tvpiInt.h"

/**********************************************************************
 * create an integer constant
 *********************************************************************/
constant_t tvpi_create_int_cst(int v)
{
  tvpi_cst_t *res = (tvpi_cst_t*)malloc(sizeof(tvpi_cst_t));
  res->type = TVPI_INT;
  res->int_val = v;
  return (constant_t)res;
}

/**********************************************************************
 * create a rational constant. we use the div_t datatype to store the
 * numerator and denominator.
 *********************************************************************/
constant_t tvpi_create_rat_cst(int n,int d)
{
  tvpi_cst_t *res = (tvpi_cst_t*)malloc(sizeof(tvpi_cst_t));
  res->type = TVPI_RAT;
  mpq_init(res->rat_val);
  mpq_set_si(res->rat_val,n,d);
  mpq_canonicalize(res->rat_val);
  return (constant_t)res;
}

/**********************************************************************
 * create a double constant
 *********************************************************************/
constant_t tvpi_create_double_cst(double v)
{
  tvpi_cst_t *res = (tvpi_cst_t*)malloc(sizeof(tvpi_cst_t));
  res->type = TVPI_DBL;
  res->dbl_val = v;
  return (constant_t)res;
}

/**********************************************************************
 * create -1*c in place
 *********************************************************************/
void tvpi_negate_cst_inplace (tvpi_cst_t *c)
{
  switch(c->type)
    {
    case TVPI_INT:
      if(c->int_val == INT_MAX) c->int_val = INT_MIN;
      else if(c->int_val == INT_MIN) c->int_val = INT_MAX;
      else c->int_val = -(c->int_val);
      break;
    case TVPI_RAT:
      if(mpz_get_si(mpq_numref(c->rat_val)) == INT_MAX) {
        mpz_set_si(mpq_numref(c->rat_val),INT_MIN);
      } else if(mpz_get_si(mpq_numref(c->rat_val)) == INT_MIN) {
        mpz_set_si(mpq_numref(c->rat_val),INT_MAX);
      } else mpz_neg(mpq_numref(c->rat_val),mpq_numref(c->rat_val));
      break;
    case TVPI_DBL:
      if(c->dbl_val == DBL_MAX) c->dbl_val = DBL_MIN;
      else if(c->dbl_val == DBL_MIN) c->dbl_val = DBL_MAX;
      else c->dbl_val = -(c->dbl_val);
      return;
    default:
      break;
    }
}

/**********************************************************************
 * Return -1*c -- this one allocates new memory
 *********************************************************************/
constant_t tvpi_negate_cst (constant_t c)
{
  tvpi_cst_t *x = tvpi_dup_cst((tvpi_cst_t*)c);
  tvpi_negate_cst_inplace(x);
  return (constant_t)x;
}

/**********************************************************************
 * Compares c1 and c2 for =
 * Returns true if c1 and c2 are of same type and c1 = c2
 * Returns false otherwise
 *********************************************************************/
bool tvpi_cst_eq (constant_t c1,constant_t c2)
{
  tvpi_cst_t *x1 = (tvpi_cst_t*)c1;
  tvpi_cst_t *x2 = (tvpi_cst_t*)c2;

  if(x1->type != x2->type) return 0;

  switch(x1->type)
    {
    case TVPI_INT:
      return (x1->int_val == x2->int_val);
    case TVPI_RAT:
      if(tvpi_is_pinf_cst(c1)) return tvpi_is_pinf_cst(c2);
      if(tvpi_is_ninf_cst(c1)) return tvpi_is_ninf_cst(c2);
      if(tvpi_is_pinf_cst(c2)) return tvpi_is_pinf_cst(c1);
      if(tvpi_is_ninf_cst(c2)) return tvpi_is_ninf_cst(c1);
      return mpq_equal(x1->rat_val,x2->rat_val);
    case TVPI_DBL:
      return (x1->dbl_val == x2->dbl_val);
    default:
      return 0;
    }
}

/**********************************************************************
 * Compares c1 and c2 for <
 * Returns true if c1 and c2 are of same type and c1 < c2
 * Returns false otherwise
 *********************************************************************/
bool tvpi_cst_lt (constant_t c1,constant_t c2)
{
  tvpi_cst_t *x1 = (tvpi_cst_t*)c1;
  tvpi_cst_t *x2 = (tvpi_cst_t*)c2;

  if(x1->type != x2->type) return 0;

  switch(x1->type)
    {
    case TVPI_INT:
      return (x1->int_val < x2->int_val);
    case TVPI_RAT:
      if(tvpi_is_pinf_cst(c1)) return 0;
      if(tvpi_is_pinf_cst(c2)) return !tvpi_is_pinf_cst(c1);
      if(tvpi_is_ninf_cst(c1)) return !tvpi_is_ninf_cst(c2);
      if(tvpi_is_ninf_cst(c2)) return 0;
      return mpq_cmp(x1->rat_val,x2->rat_val) < 0;
    case TVPI_DBL:
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
bool tvpi_cst_le (constant_t c1,constant_t c2)
{
  tvpi_cst_t *x1 = (tvpi_cst_t*)c1;
  tvpi_cst_t *x2 = (tvpi_cst_t*)c2;

  if(x1->type != x2->type) return 0;

  switch(x1->type)
    {
    case TVPI_INT:
      return (x1->int_val <= x2->int_val);
    case TVPI_RAT:
      if(tvpi_is_pinf_cst(c1)) return tvpi_is_pinf_cst(c2);
      if(tvpi_is_pinf_cst(c2)) return 1;
      if(tvpi_is_ninf_cst(c1)) return 1;
      if(tvpi_is_ninf_cst(c2)) return tvpi_is_ninf_cst(c1);
      return mpq_cmp(x1->rat_val,x2->rat_val) <= 0;
    case TVPI_DBL:
      return (x1->dbl_val <= x2->dbl_val);
    default:
      return 0;
    }
}

/**********************************************************************
 * Return c1 + c2. If c1 and c2 are not of same type, return NULL.
 *********************************************************************/
constant_t tvpi_cst_add(constant_t c1,constant_t c2)
{
  tvpi_cst_t *x1 = (tvpi_cst_t*)c1;
  tvpi_cst_t *x2 = (tvpi_cst_t*)c2;

  if(x1->type != x2->type) return NULL;

  switch(x1->type)
    {
    case TVPI_INT:
      return tvpi_create_int_cst(x1->int_val + x2->int_val);
    case TVPI_RAT:
      {
        tvpi_cst_t *res = (tvpi_cst_t*)malloc(sizeof(tvpi_cst_t));
        res->type = TVPI_RAT;
        mpq_init(res->rat_val);
        mpq_add(res->rat_val,x1->rat_val,x2->rat_val);
        return (constant_t)res;
      }
    case TVPI_DBL:
      return tvpi_create_double_cst(x1->dbl_val + x2->dbl_val);
    default:
      return 0;
    }
}


/**********************************************************************
 * return true if the argument is positive infinity
 *********************************************************************/
bool tvpi_is_pinf_cst(constant_t c)
{
  tvpi_cst_t *x = (tvpi_cst_t*)c;
  switch(x->type)
    {
    case TVPI_INT:
      return x->int_val == INT_MAX;
    case TVPI_RAT:
      return (mpz_get_si(mpq_numref(x->rat_val)) == INT_MAX);
    case TVPI_DBL:
      return (x->dbl_val == DBL_MAX);
    default:
      return 0;
    }
}

/**********************************************************************
 * return true if the argument is negative infinity
 *********************************************************************/
bool tvpi_is_ninf_cst(constant_t c)
{
  tvpi_cst_t *x = (tvpi_cst_t*)c;
  switch(x->type)
    {
    case TVPI_INT:
      return x->int_val == INT_MIN;
    case TVPI_RAT:
      return (mpz_get_si(mpq_numref(x->rat_val)) == INT_MIN);
    case TVPI_DBL:
      return (x->dbl_val == DBL_MIN);
    default:
      return 0;
    }
}

/**********************************************************************
 * destroy a constant
 *********************************************************************/
void tvpi_destroy_cst(constant_t c)
{
  tvpi_cst_t *x = (tvpi_cst_t*)c;
  if(x->type == TVPI_RAT) mpq_clear(x->rat_val);
  free(x);
}

/**********************************************************************
 * Create a linear term: the first argument is an array of variable
 * coefficients. the second argument is the size of the array of
 * coefficients.
 *********************************************************************/
linterm_t tvpi_create_linterm(int* coeffs, size_t n)
{
  tvpi_term_t *res = (tvpi_term_t*)malloc(sizeof(tvpi_term_t));
  memset((void*)(res),0,sizeof(tvpi_term_t));
  size_t i = 0;
  for(;i < n;++i) {
    if(coeffs[i]) {
      if(res->coeff1) {
        res->coeff2 = coeffs[i];
        res->var2 = i;
      } else {
        res->coeff1 = coeffs[i];
        res->var1 = i;
      }
    }
  }
  return (linterm_t)res;
}

/**********************************************************************
 * Returns true if t1 is the same term as t2
 *********************************************************************/
bool tvpi_term_equals(linterm_t t1, linterm_t t2)
{
  tvpi_term_t *x1 = (tvpi_term_t*)t1;
  tvpi_term_t *x2 = (tvpi_term_t*)t2;
  return (x1->coeff1 == x2->coeff1 && x1->var1 == x2->var1 && 
          x1->coeff2 == x2->coeff2 && x1->var2 == x2->var2);
}

/**********************************************************************
 * Returns true if there exists a variable v in the set var whose
 * coefficient in t is non-zero.

 * t is a term, var is represented as an array of booleans, and n is
 * the size of var.
 *********************************************************************/
bool tvpi_term_has_var (linterm_t t,bool *vars)
{
  tvpi_term_t *x = (tvpi_term_t*)t;
  return vars[x->var1] || vars[x->var2];
}

/**********************************************************************
 * Returns the number of variables of the theory
 *********************************************************************/
size_t tvpi_num_of_vars(theory_t* self)
{
  return ((tvpi_theory_t*)self)->var_num;
}

/**********************************************************************
 * Create a term given its two variables. This is a private function.
 *********************************************************************/
linterm_t _tvpi_create_linterm(int cf1,int v1,int cf2,int v2)
{
  tvpi_term_t *res = (tvpi_term_t*)malloc(sizeof(tvpi_term_t));
  //ensure canonical form, i.e., v1 < v2
  if(v1 < v2) {
    res->coeff1 = cf1;
    res->var1 = v1;
    res->coeff2 = cf2;
    res->var2 = v2;
  } else {
    res->coeff1 = cf2;
    res->var1 = v2;
    res->coeff2 = cf1;
    res->var2 = v1;
  }
  return (linterm_t)res;
}

/**********************************************************************
 * Return the result of resolving t1 and t2. If the resolvant does not
 * exist, return NULL.
 *********************************************************************/
linterm_t _tvpi_terms_have_resolvent(linterm_t t1, linterm_t t2, int x)
{
  tvpi_term_t *x1 = (tvpi_term_t*)t1;
  tvpi_term_t *x2 = (tvpi_term_t*)t2;
  //first and first variables cancel
  if(x1->var1 == x2->var1 && x1->var1 == x && 
     x1->coeff1 == -(x2->coeff1) && x1->var2 != x2->var2) {
    return _tvpi_create_linterm(x1->coeff2,x1->var2,x2->coeff2,x2->var2);
  }
  //first and second variables cancel
  if(x1->var1 == x2->var2 && x1->var1 == x && 
     x1->coeff1 == -(x2->coeff2) && x1->var2 != x2->var1) {
    return _tvpi_create_linterm(x1->coeff2,x1->var2,x2->coeff1,x2->var1);
  }
  //second and first variables cancel
  if(x1->var2 == x2->var1 && x1->var2 == x && 
     x1->coeff2 == -(x2->coeff1) && x1->var1 != x2->var2) {
    return _tvpi_create_linterm(x1->coeff1,x1->var1,x2->coeff2,x2->var2);
  }
  //second and second variables cancel
  if(x1->var2 == x2->var2 && x1->var2 == x && 
     x1->coeff2 == -(x2->coeff2) && x1->var1 != x2->var1) {
    return _tvpi_create_linterm(x1->coeff1,x1->var1,x2->coeff1,x2->var1);
  }
  //no resolvent
  return NULL;
}



/**********************************************************************
 * Returns >0 if t1 and t2 have a resolvent on variable x, 
 * Returns <0 if t1 and -t2 have a resolvent on variable x
 * Return 0 if t1 and t2 do not resolve.
 *********************************************************************/
int tvpi_terms_have_resolvent(linterm_t t1, linterm_t t2, int x)
{
  tvpi_term_t *x1 = (tvpi_term_t*)t1;
  tvpi_term_t *x2 = (tvpi_term_t*)t2;
  //first and first variables cancel
  if(x1->var1 == x2->var1 && x1->var1 == x && x1->var2 != x2->var2) {
    return (x1->coeff1 == -(x2->coeff1)) ? 1 : (x1->coeff1 == x2->coeff1 ? -1 : 0);
  }
  //first and second variables cancel
  if(x1->var1 == x2->var2 && x1->var1 == x && x1->var2 != x2->var1) {
    return (x1->coeff1 == -(x2->coeff2)) ? 1 : (x1->coeff1 == x2->coeff2 ? -1 : 0);
  }
  //second and first variables cancel
  if(x1->var2 == x2->var1 && x1->var2 == x && x1->var1 != x2->var2) {
    return (x1->coeff2 == -(x2->coeff1)) ? 1 : (x1->coeff2 == x2->coeff1 ? -1 : 0);
  }
  //second and second variables cancel
  if(x1->var2 == x2->var2 && x1->var2 == x && x1->var1 != x2->var1) {
    return (x1->coeff2 == -(x2->coeff2)) ? 1 : (x1->coeff2 == x2->coeff2 ? -1 : 0);
  }
  //no resolution
  return 0;
}

/**********************************************************************
 * create -1*t in place -- negates the two coefficients -- variables
 * are left unchanged to preserve canonicity
 *********************************************************************/
void tvpi_negate_term_inplace(tvpi_term_t *t)
{
  t->coeff1 = -(t->coeff1);
  t->coeff2 = -(t->coeff2);
}

/**********************************************************************
 * return -1*t
 *********************************************************************/
linterm_t tvpi_negate_term(linterm_t t)
{
  tvpi_term_t *x = tvpi_dup_term((tvpi_term_t*)t);
  tvpi_negate_term_inplace(x);
  return (linterm_t)x;
}

/**********************************************************************
 * Returns a variable that has a non-zero coefficient in t. Returns <0
 * if no such variable exists.
 *********************************************************************/
int tvpi_pick_var (linterm_t t, bool* vars)
{
  tvpi_term_t *x = (tvpi_term_t*)t;
  if(vars[x->var1]) return x->var1;
  if(vars[x->var2]) return x->var2;
  return -1;
}

/**********************************************************************
 * reclaim resources allocated by t
 *********************************************************************/
void tvpi_destroy_term(linterm_t t)
{
  free((tvpi_term_t*)t);
}

/**********************************************************************
 * Creates a linear contraint t < k (if s is true) t<=k (if s is false)
 *********************************************************************/
lincons_t tvpi_create_rat_cons(linterm_t t, bool s, constant_t k)
{
  tvpi_cons_t *res = (tvpi_cons_t*)malloc(sizeof(tvpi_cons_t));
  res->term = tvpi_dup_term((tvpi_term_t*)t);
  res->cst = tvpi_dup_cst((tvpi_cst_t*)k);
  res->strict = s;
  return (lincons_t)res;
}

/**********************************************************************
 * Creates a linear contraint t < k (if s is true) t<=k (if s is false)
 *********************************************************************/
lincons_t tvpi_create_int_cons(linterm_t t, bool s, constant_t k)
{
  tvpi_cons_t *res = (tvpi_cons_t*)malloc(sizeof(tvpi_cons_t));
  res->term = tvpi_dup_term((tvpi_term_t*)t);
  res->cst = tvpi_dup_cst((tvpi_cst_t*)k);

  /* convert '<' inequalities to '<=' */
  if (s && !tvpi_is_pinf_cst(&(res->cst)) && !tvpi_is_ninf_cst(&(res->cst)))
    res->cst->int_val--;

  /* all integer constraints are non-strict */
  res->strict = 0;

  return (lincons_t)res;
}


/**********************************************************************
 * Returns true if l is a strict constraint
 *********************************************************************/
bool tvpi_is_strict(lincons_t l)
{
  tvpi_cons_t *x = (tvpi_cons_t*)l;
  return x->strict;
}

/**********************************************************************
 * duplicate a term. this is a private function.
 *********************************************************************/
tvpi_term_t *tvpi_dup_term(tvpi_term_t *arg)
{
  tvpi_term_t *res = (tvpi_term_t*)malloc(sizeof(tvpi_term_t));
  *res = *arg;
  return res;
}

/**********************************************************************
 * get the term corresponding to the argument constraint -- the
 * returned value should NEVER be freed by the user.
 *********************************************************************/
linterm_t tvpi_get_term(lincons_t l)
{
  tvpi_cons_t *x = (tvpi_cons_t*)l;  
  return (linterm_t)(x->term);
}

/**********************************************************************
 * duplicate a constant. this is a private function.
 *********************************************************************/
tvpi_cst_t *tvpi_dup_cst(tvpi_cst_t *arg)
{
  tvpi_cst_t *res = (tvpi_cst_t*)malloc(sizeof(tvpi_cst_t));
  if(arg->type == TVPI_RAT) {
    res->type = TVPI_RAT;
    mpq_init(res->rat_val);
    mpq_set(res->rat_val,arg->rat_val);
  } else *res = *arg;
  return res;
}

/**********************************************************************
 * get the constant corresponding to the argument constraint -- the
 * returned value should NEVER be freed by the user.
 *********************************************************************/
constant_t tvpi_get_constant(lincons_t l)
{
  tvpi_cons_t *x = (tvpi_cons_t*)l;  
  return (constant_t)(x->cst);
}

/**********************************************************************
 * Complements a linear constraint
 *********************************************************************/
lincons_t tvpi_negate_int_cons(lincons_t l)
{
  lincons_t res = tvpi_create_int_cons(tvpi_get_term(l),!tvpi_is_strict(l),
                                       tvpi_get_constant(l));
  tvpi_negate_term_inplace(tvpi_get_term(res));
  tvpi_negate_cst_inplace(tvpi_get_constant(res));
  return res;
}

lincons_t tvpi_negate_rat_cons(lincons_t l)
{
  lincons_t res = tvpi_create_rat_cons(tvpi_get_term(l),!tvpi_is_strict(l),
                                       tvpi_get_constant(l));
  tvpi_negate_term_inplace(tvpi_get_term(res));
  tvpi_negate_cst_inplace(tvpi_get_constant(res));
  return res;
}


/**********************************************************************
 * Returns true if l is a negative constraint (i.e., the smallest
 * non-zero dimension has a negative coefficient.)
 *********************************************************************/
bool tvpi_is_negative_cons(lincons_t l)
{
  linterm_t x = tvpi_get_term(l);
  tvpi_term_t *y = (tvpi_term_t*)x;
  bool res = (y->coeff1 == -1);
  return res;
}

/**********************************************************************
 * If is_stronger_cons(l1, l2) then l1 implies l2
 *********************************************************************/
bool tvpi_is_stronger_cons(lincons_t l1, lincons_t l2)
{
  //get the terms and constants
  linterm_t x1 = tvpi_get_term(l1);
  linterm_t x2 = tvpi_get_term(l2);
  constant_t a1 = tvpi_get_constant(l1);
  constant_t a2 = tvpi_get_constant(l2);

#ifdef DEBUG
  tvpi_term_t *y1 = (tvpi_term_t*)x1;
  tvpi_term_t *y2 = (tvpi_term_t*)x2;
  printf ("is_stronger_cons ( x%d - x%d %s %d with x%d - x%d %s %d )\n",
	  y1->var1, y1->var2, (tvpi_is_strict (l1) ? "<" : "<="), 
	  ((tvpi_cst_t*) a1)->int_val, 
	  y2->var1, y2->var2, (tvpi_is_strict (l2) ? "<" : "<="), 
	  ((tvpi_cst_t*) a2)->int_val);
#endif

  //if the terms are different return false
  if(!tvpi_term_equals(x1,x2)) return 0;

  /*
   * We assume that all integer constraints are non-strict, i.e., of
   * the form t1 <= c.
   */

  if (!tvpi_is_strict (l1) && tvpi_is_strict (l2))
    return tvpi_cst_lt(a1, a2);
  return tvpi_cst_le (a1, a2);  
}

/**********************************************************************
 * Computes the resolvent of constraints l1 and l2 from an integer
 * theory on x. Returns NULL if there is no resolvent.
 *********************************************************************/
lincons_t tvpi_resolve_int_cons(lincons_t l1, lincons_t l2, int x)
{
  //get the constants
  constant_t c1 = tvpi_get_constant(l1);
  constant_t c2 = tvpi_get_constant(l2);

  //if any of the constants is infinity, there is no resolvant
  if(tvpi_is_pinf_cst(c1) || tvpi_is_ninf_cst(c1) ||
     tvpi_is_pinf_cst(c2) || tvpi_is_ninf_cst(c2)) return NULL;

  //get the terms
  linterm_t t1 = tvpi_get_term(l1);
  linterm_t t2 = tvpi_get_term(l2);

  //if there is no resolvent between t1 and t2
  linterm_t t3 = _tvpi_terms_have_resolvent(t1,t2,x);
  if(!t3) return NULL; 

  /*  X-Y <= C1 and Y-Z <= C2 ===> X-Z <= C1+C2 */
  constant_t c3 = tvpi_cst_add(c1,c2);
  lincons_t res = tvpi_create_int_cons(t3,0,c3);
  tvpi_destroy_term(t3);
  tvpi_destroy_cst(c3);      
  return res;
}

/**********************************************************************
 * Computes the resolvent of constraints l1 and l2 from a rational
 * theory on x. Returns NULL if there is no resolvent.
 *********************************************************************/
lincons_t tvpi_resolve_rat_cons(lincons_t l1, lincons_t l2, int x)
{
  //get the constants
  constant_t c1 = tvpi_get_constant(l1);
  constant_t c2 = tvpi_get_constant(l2);

  //if any of the constants is infinity, there is no resolvant
  if(tvpi_is_pinf_cst(c1) || tvpi_is_ninf_cst(c1) ||
     tvpi_is_pinf_cst(c2) || tvpi_is_ninf_cst(c2)) return NULL;

  //get the terms
  linterm_t t1 = tvpi_get_term(l1);
  linterm_t t2 = tvpi_get_term(l2);

  //if there is no resolvent between t1 and t2
  linterm_t t3 = _tvpi_terms_have_resolvent(t1,t2,x);
  if(!t3) return NULL;

  //X-Y <= C1 and Y-Z <= C2 ===> X-Z <= C1+C2
  if(!tvpi_is_strict(l1) && !tvpi_is_strict(l2)) {
    constant_t c3 = tvpi_cst_add(c1,c2);
    lincons_t res = tvpi_create_rat_cons(t3,0,c3);
    tvpi_destroy_term(t3);
    tvpi_destroy_cst(c3);
    return res;
  }

  //for all other cases, X-Z < C1+C2
  constant_t c3 = tvpi_cst_add(c1,c2);
  lincons_t res = tvpi_create_rat_cons(t3,1,c3);
  tvpi_destroy_term(t3);
  tvpi_destroy_cst(c3);
  return res;
}
  
/**********************************************************************
 * destroy a linear constraint
 *********************************************************************/
void tvpi_destroy_lincons(lincons_t l)
{
  tvpi_destroy_term(tvpi_get_term(l));
  tvpi_destroy_cst(tvpi_get_constant(l));
  free((tvpi_cons_t*)l);
}
  
/**********************************************************************
 * copy a linear constraint
 *********************************************************************/
lincons_t tvpi_dup_lincons(lincons_t l)
{
  tvpi_cons_t *x = (tvpi_cons_t*)l;
  tvpi_cons_t *res = (tvpi_cons_t*)malloc(sizeof(tvpi_cons_t));
  res->term = tvpi_dup_term(x->term);
  res->cst = tvpi_dup_cst(x->cst);
  res->strict = x->strict;
  return (lincons_t)res;
}

/**********************************************************************
 * recursively go through a list of tvpi_cons_node_t and return the
 * tdd_node* for an element whose cons matches with c. if no such node
 * exists, create one at the right spot.
 *********************************************************************/
tdd_node *tvpi_get_node(tdd_manager* m,tvpi_cons_node_t *curr,
                       tvpi_cons_node_t *prev,tvpi_cons_t *c)
{
  //if at the end of the list -- create a fresh tdd_node and insert it
  //at the end of the list
  if(curr == NULL) {
    tvpi_cons_node_t *cn = 
      (tvpi_cons_node_t*)malloc(sizeof(tvpi_cons_node_t));
    cn->cons = *c;
    cn->node = tdd_new_var(m,(lincons_t)c);
    //if not at the start of the list
    if(prev) {
      cn->next = prev->next;
      prev->next = cn;
    }
    //if at the start of the list
    else {
      tvpi_theory_t *theory = (tvpi_theory_t*)m->theory;
      cn->next = theory->cons_node_map[c->term->var1][c->term->var2];
      theory->cons_node_map[c->term->var1][c->term->var2] = cn;
    }
    return cn->node;
  }

  //if i found a matching element, return it
  if(tvpi_term_equals(&(curr->cons.term),&(c->term)) &&
     ((tvpi_is_strict(&(curr->cons)) && tvpi_is_strict(c)) ||
      (!tvpi_is_strict(&(curr->cons)) && !tvpi_is_strict(c))) &&
     tvpi_cst_eq(&(curr->cons.cst),&(c->cst))) return curr->node;

  //if the c implies curr, then add c just before curr
  if(m->theory->is_stronger_cons(c,&(curr->cons))) {
    tvpi_cons_node_t *cn = 
      (tvpi_cons_node_t*)malloc(sizeof(tvpi_cons_node_t));
    cn->cons = *c;
    cn->node = tdd_new_var_before(m,curr->node,(lincons_t)c);
    //if not at the start of the list
    if(prev) {
      cn->next = prev->next;
      prev->next = cn;
    }
    //if at the start of the list
    else {
      tvpi_theory_t *theory = (tvpi_theory_t*)m->theory;
      cn->next = theory->cons_node_map[c->term->var1][c->term->var2];
      theory->cons_node_map[c->term->var1][c->term->var2] = cn;
    }
    return cn->node;
  }

  //try recursively with the next element
  return tvpi_get_node(m,curr->next,curr,c);
}

/**********************************************************************
 * return a TDD node corresponding to l
 *********************************************************************/
tdd_node* tvpi_to_tdd(tdd_manager* m, lincons_t l)
{
  tvpi_theory_t *theory = (tvpi_theory_t*)m->theory;

  //negate the constraint if necessary
  bool neg = theory->base.is_negative_cons(l);
  if(neg) l = theory->base.negate_cons (l);

  //convert to right type
  tvpi_cons_t *c = (tvpi_cons_t*)l;

  //find the right node. create one if necessary.
  tdd_node *res = 
    tvpi_get_node(m,theory->cons_node_map[c->term->var1][c->term->var2],NULL,c);

  //cleanup
  if(neg) {
    res = tdd_not(res);
    tvpi_destroy_lincons(l);
  }
  
  //all done
  return res;
}

/**********************************************************************
 * common steps when creating any theory - argument is the number of
 * variables
 *********************************************************************/
tvpi_theory_t *tvpi_create_theory_common(size_t vn)
{
  tvpi_theory_t *res = (tvpi_theory_t*)malloc(sizeof(tvpi_theory_t));
  memset((void*)(res),0,sizeof(tvpi_theory_t));
  res->base.create_int_cst = tvpi_create_int_cst;
  res->base.create_rat_cst = tvpi_create_rat_cst;
  res->base.create_double_cst = tvpi_create_double_cst;
  res->base.negate_cst = tvpi_negate_cst;
  res->base.is_pinf_cst = tvpi_is_pinf_cst;
  res->base.is_ninf_cst = tvpi_is_ninf_cst;
  res->base.destroy_cst = tvpi_destroy_cst;
  res->base.create_linterm = tvpi_create_linterm;
  res->base.term_equals = tvpi_term_equals;
  res->base.term_has_var = tvpi_term_has_var;
  res->base.num_of_vars = tvpi_num_of_vars;
  res->base.terms_have_resolvent = tvpi_terms_have_resolvent;
  res->base.negate_term = tvpi_negate_term;
  res->base.pick_var = tvpi_pick_var;
  res->base.destroy_term = tvpi_destroy_term;
  res->base.is_strict = tvpi_is_strict;
  res->base.get_term = tvpi_get_term;
  res->base.get_constant = tvpi_get_constant;
  res->base.is_negative_cons = tvpi_is_negative_cons;
  res->base.is_stronger_cons = tvpi_is_stronger_cons;
  res->base.destroy_lincons = tvpi_destroy_lincons;
  res->base.dup_lincons = tvpi_dup_lincons;
  res->base.to_tdd = tvpi_to_tdd;
  res->var_num = vn;
  //create maps from constraints to DD nodes -- one per variable pair
  res->cons_node_map = (tvpi_cons_node_t ***)malloc(vn * sizeof(tvpi_cons_node_t **));
  size_t i = 0;
  for(;i < vn;++i) {
    res->cons_node_map[i] = (tvpi_cons_node_t **)malloc(vn * sizeof(tvpi_cons_node_t *));
    size_t j = 0;
    for(;j < vn;++j) res->cons_node_map[i][j] = NULL;
  }
  return res;
}

/**********************************************************************
 * create a TVPI theory of integers - the argument is the number of
 * variables
 *********************************************************************/
theory_t *tvpi_create_int_theory(size_t vn)
{
  tvpi_theory_t *res = tvpi_create_theory_common(vn);
  res->base.create_cons = tvpi_create_int_cons;
  res->base.negate_cons = tvpi_negate_int_cons;
  res->base.resolve_cons = tvpi_resolve_int_cons;
  res->type = TVPI_INT;
  return (theory_t*)res;
}

/**********************************************************************
 * create a TVPI theory of rationals - the argument is the number of
 * variables
 *********************************************************************/
theory_t *tvpi_create_rat_theory(size_t vn)
{
  tvpi_theory_t *res = tvpi_create_theory_common(vn);
  res->base.create_cons = tvpi_create_rat_cons;
  res->base.negate_cons = tvpi_negate_rat_cons;
  res->base.resolve_cons = tvpi_resolve_rat_cons;
  res->type = TVPI_RAT;
  return (theory_t*)res;
}

/**********************************************************************
 * destroy a TVPI theory
 *********************************************************************/
void tvpi_destroy_theory(theory_t *t)
{
  //free the cons_node_map
  tvpi_cons_node_t ***cnm = ((tvpi_theory_t*)t)->cons_node_map;
  size_t vn = ((tvpi_theory_t*)t)->var_num;
  size_t i = 0;
  for(;i < vn;++i) {
    size_t j = 0;
    for(;j < vn;++j) {
      tvpi_cons_node_t *curr = cnm[i][j];
      while(curr) {
        tvpi_cons_node_t *next = curr->next;
        free(curr);
        curr = next;
      }
    }
    free(cnm[i]);
  }
  free(cnm);

  //free the theory
  free((tvpi_theory_t*)t);
}

/**********************************************************************
 * end of tdd-tvpi.c
 *********************************************************************/

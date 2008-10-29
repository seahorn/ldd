/**********************************************************************
 * The main file that provides the TVPI theory.
 *********************************************************************/

#include "tdd-tvpiInt.h"

/**********************************************************************
 * create an integer constant
 *********************************************************************/
constant_t tvpi_create_int_cst(int v)
{
  return tvpi_create_rat_cst(v,1);
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
    case TVPI_RAT:
      if(mpz_get_si(mpq_numref(c->rat_val)) == INT_MAX) {
        mpz_set_si(mpq_numref(c->rat_val),INT_MIN);
      } else if(mpz_get_si(mpq_numref(c->rat_val)) == INT_MIN) {
        mpz_set_si(mpq_numref(c->rat_val),INT_MAX);
      } else mpq_neg(c->rat_val,c->rat_val);
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
 * multiply c1 by the absolute value of c2
 *********************************************************************/
constant_t tvpi_cst_mul(constant_t c1,mpq_t c2)
{
  tvpi_cst_t *x1 = (tvpi_cst_t*)c1;

  switch(x1->type)
    {
    case TVPI_RAT:
      {
        tvpi_cst_t *res = (tvpi_cst_t*)malloc(sizeof(tvpi_cst_t));
        res->type = TVPI_RAT;
        mpq_init(res->rat_val);
        mpq_mul(res->rat_val,x1->rat_val,c2);
        if(mpq_sgn(c2) < 0) mpq_neg(res->rat_val,res->rat_val);
        return (constant_t)res;
      }
    case TVPI_DBL:
      return tvpi_create_double_cst(x1->dbl_val * mpq_get_d(c2) * mpq_sgn(c2));
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
  mpq_init(res->coeffs[0]);
  mpq_init(res->coeffs[1]);
  size_t i = 0;
  for(;i < n;++i) {
    if(coeffs[i]) {
      if(mpq_sgn(res->coeffs[0])) {
        mpq_set_si(res->coeffs[1],coeffs[i],1);
        res->vars[1] = i;
      } else {
        mpq_set_si(res->coeffs[0],coeffs[i],1);
        res->vars[0] = i;
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
  return (mpq_equal(x1->coeffs[0],x2->coeffs[0]) && x1->vars[0] == x2->vars[0] && 
          mpq_equal(x1->coeffs[1],x2->coeffs[1]) && x1->vars[1] == x2->vars[1]);
}

/**********************************************************************
 * Returns true if term t has variable v
 *********************************************************************/
bool tvpi_term_has_var (linterm_t t,int var)
{
  tvpi_term_t *x = (tvpi_term_t*)t;
  return (x->vars[0] == var) || (x->vars[1] == var);
}

/**********************************************************************
 * Returns true if there exists a variable v in the set var whose
 * coefficient in t is non-zero.

 * t is a term, var is represented as an array of booleans, and n is
 * the size of var.
 *********************************************************************/
bool tvpi_term_has_vars (linterm_t t,bool *vars)
{
  tvpi_term_t *x = (tvpi_term_t*)t;
  return vars[x->vars[0]] || vars[x->vars[1]];
}

/**********************************************************************
 * Returns the number of variables of the theory
 *********************************************************************/
size_t tvpi_num_of_vars(theory_t* self)
{
  return ((tvpi_theory_t*)self)->var_num;
}

/**********************************************************************
 * Create a term given its two variables and their coefficients. Each
 * coefficient is provided as a pair of rational numbers X and Y. The
 * actual coefficient is obtained by multiplying X and the absolute
 * value of Y. This is a private function.
 *********************************************************************/
linterm_t _tvpi_create_linterm(mpq_t cf11,mpq_t cf12,int v1,
                               mpq_t cf21,mpq_t cf22,int v2)
{
  tvpi_term_t *res = (tvpi_term_t*)malloc(sizeof(tvpi_term_t));
  mpq_init(res->coeffs[0]);
  mpq_init(res->coeffs[1]);
  //ensure canonical form, i.e., v1 < v2
  if(v1 < v2) {
    mpq_mul(res->coeffs[0],cf11,cf12);
    if(mpq_sgn(cf12) < 0) mpq_neg(res->coeffs[0],res->coeffs[0]);
    res->vars[0] = v1;
    mpq_mul(res->coeffs[1],cf21,cf22);
    if(mpq_sgn(cf22) < 0) mpq_neg(res->coeffs[1],res->coeffs[1]);
    res->vars[1] = v2;
  } else {
    mpq_mul(res->coeffs[0],cf21,cf22);
    if(mpq_sgn(cf22) < 0) mpq_neg(res->coeffs[0],res->coeffs[0]);
    res->vars[0] = v2;
    mpq_mul(res->coeffs[1],cf11,cf12);
    if(mpq_sgn(cf12) < 0) mpq_neg(res->coeffs[1],res->coeffs[1]);
    res->vars[1] = v1;
  }
  return (linterm_t)res;
}

/**********************************************************************
 * print a constant
 *********************************************************************/
void tvpi_print_cst(FILE *f,tvpi_cst_t *c)
{
  switch(c->type) {
  case TVPI_RAT:
    mpq_out_str(f,10,c->rat_val);
    break;
  case TVPI_DBL:
    fprintf(f,"%lf",c->dbl_val);
    break;
  default:
    break;
  }
}

/**********************************************************************
 * print a term
 *********************************************************************/
void tvpi_print_term(FILE *f,tvpi_term_t *t)
{
  mpq_out_str(f,10,t->coeffs[0]);
  fprintf(f," * %d + ",t->vars[0]);
  mpq_out_str(f,10,t->coeffs[1]);
  fprintf(f," * %d",t->vars[1]);
}

/**********************************************************************
 * print a constraint - this one takes a tvpi_cons_t* as input
 *********************************************************************/
void tvpi_print_cons(FILE *f,tvpi_cons_t *l)
{
  tvpi_print_term(f,l->term);
  fprintf(f," %s ",l->strict ? "<" : "<=");
  tvpi_print_cst(f,l->cst);
}

/**********************************************************************
 * Return the result of resolving t1 and t2. If the resolvant does not
 * exist, return NULL.
 *********************************************************************/
tvpi_resolve_t _tvpi_terms_have_resolvent(tvpi_term_t *x1,tvpi_term_t *x2, int x)
{
  tvpi_resolve_t res;
  res.term = NULL; 
  //first and first variables cancel
  if(x1->vars[0] == x2->vars[0] && x1->vars[0] == x && 
     mpq_sgn(x1->coeffs[0]) == -(mpq_sgn(x2->coeffs[0])) && x1->vars[1] != x2->vars[1]) {
    res.term = _tvpi_create_linterm(x1->coeffs[1],x2->coeffs[0],x1->vars[1],
                                    x2->coeffs[1],x1->coeffs[0],x2->vars[1]);
    res.cst1 = 0;
    res.cst2 = 0;
  }
  //first and second variables cancel
  if(x1->vars[0] == x2->vars[1] && x1->vars[0] == x && 
     mpq_sgn(x1->coeffs[0]) == -(mpq_sgn(x2->coeffs[1])) && x1->vars[1] != x2->vars[0]) {
    res.term = _tvpi_create_linterm(x1->coeffs[1],x2->coeffs[1],x1->vars[1],
                                    x2->coeffs[0],x1->coeffs[0],x2->vars[0]);
    res.cst1 = 1;
    res.cst2 = 0;
  }
  //second and first variables cancel
  if(x1->vars[1] == x2->vars[0] && x1->vars[1] == x && 
     mpq_sgn(x1->coeffs[1]) == -(mpq_sgn(x2->coeffs[0])) && x1->vars[0] != x2->vars[1]) {
    res.term = _tvpi_create_linterm(x1->coeffs[0],x2->coeffs[0],x1->vars[0],
                                    x2->coeffs[1],x1->coeffs[1],x2->vars[1]);
    res.cst1 = 0;
    res.cst2 = 1;
  }
  //second and second variables cancel
  if(x1->vars[1] == x2->vars[1] && x1->vars[1] == x && 
     mpq_sgn(x1->coeffs[1]) == -(mpq_sgn(x2->coeffs[1])) && x1->vars[0] != x2->vars[0]) {
    res.term = _tvpi_create_linterm(x1->coeffs[0],x2->coeffs[1],x1->vars[0],
                                    x2->coeffs[0],x1->coeffs[1],x2->vars[0]);
    res.cst1 = 1;
    res.cst2 = 1;
  }
  //all done
  return res;
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
  if(x1->vars[0] == x2->vars[0] && x1->vars[0] == x && x1->vars[1] != x2->vars[1]) {
    return (mpq_sgn(x1->coeffs[0]) == -(mpq_sgn(x2->coeffs[0]))) ? 1 : 
      (mpq_sgn(x1->coeffs[0]) == mpq_sgn(x2->coeffs[0]) ? -1 : 0);
  }
  //first and second variables cancel
  if(x1->vars[0] == x2->vars[1] && x1->vars[0] == x && x1->vars[1] != x2->vars[0]) {
    return (mpq_sgn(x1->coeffs[0]) == -(mpq_sgn(x2->coeffs[1]))) ? 1 : 
      (mpq_sgn(x1->coeffs[0]) == mpq_sgn(x2->coeffs[1]) ? -1 : 0);
  }
  //second and first variables cancel
  if(x1->vars[1] == x2->vars[0] && x1->vars[1] == x && x1->vars[0] != x2->vars[1]) {
    return (mpq_sgn(x1->coeffs[1]) == -(mpq_sgn(x2->coeffs[0]))) ? 1 : 
      (mpq_sgn(x1->coeffs[1]) == mpq_sgn(x2->coeffs[0]) ? -1 : 0);
  }
  //second and second variables cancel
  if(x1->vars[1] == x2->vars[1] && x1->vars[1] == x && x1->vars[0] != x2->vars[0]) {
    return (mpq_sgn(x1->coeffs[1]) == -(mpq_sgn(x2->coeffs[1]))) ? 1 : 
      (mpq_sgn(x1->coeffs[1]) == mpq_sgn(x2->coeffs[1]) ? -1 : 0);
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
  mpq_neg(t->coeffs[0],t->coeffs[0]);
  mpq_neg(t->coeffs[1],t->coeffs[1]);
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
  if(vars[x->vars[0]]) return x->vars[0];
  if(vars[x->vars[1]]) return x->vars[1];
  return -1;
}

/**********************************************************************
 * reclaim resources allocated by t
 *********************************************************************/
void tvpi_destroy_term(linterm_t t)
{
  tvpi_term_t *x = (tvpi_term_t*)t;
  mpq_clear(x->coeffs[0]);
  mpq_clear(x->coeffs[1]);
  free(x);
}

/**********************************************************************
 * canonicalize a constraint -- divide all coefficients and the
 * constant by the absolute value of the first coefficient so that the
 * first coefficient effectively becomes +1 or -1
 *********************************************************************/
void _tvpi_canonicalize_cons(tvpi_cons_t *l)
{
  mpq_t abs;
  mpq_init(abs);
  mpq_abs(abs,l->term->coeffs[0]);
  mpq_div(l->term->coeffs[0],l->term->coeffs[0],abs);
  mpq_div(l->term->coeffs[1],l->term->coeffs[1],abs);
  if(l->cst->type != TVPI_RAT) {
    mpq_init(l->cst->rat_val);
    mpq_set_d(l->cst->rat_val,l->cst->dbl_val);
    l->cst->type = TVPI_RAT;
  }
  mpq_div(l->cst->rat_val,l->cst->rat_val,abs);
  mpq_clear(abs);
}

/**********************************************************************
 * Creates a linear contraint t < k (if s is true) t<=k (if s is
 * false). this one does not free t and k.
 *********************************************************************/
lincons_t _tvpi_create_int_cons(linterm_t t, bool s, constant_t k)
{
  return _tvpi_create_rat_cons(t,s,k);
}

/**********************************************************************
 * Creates a linear contraint t < k (if s is true) t<=k (if s is
 * false). this one frees t and k.
 *********************************************************************/
lincons_t tvpi_create_int_cons(linterm_t t, bool s, constant_t k)
{
  lincons_t res = _tvpi_create_int_cons(t,s,k);
  tvpi_destroy_term(t);
  tvpi_destroy_cst(k);
  return res;
}

/**********************************************************************
 * Creates a linear contraint t < k (if s is true) t<=k (if s is
 * false). this one does not free t and k.
 *********************************************************************/
lincons_t _tvpi_create_rat_cons(linterm_t t, bool s, constant_t k)
{
  tvpi_cons_t *res = (tvpi_cons_t*)malloc(sizeof(tvpi_cons_t));
  res->term = tvpi_dup_term((tvpi_term_t*)t);
  res->cst = tvpi_dup_cst((tvpi_cst_t*)k);
  res->strict = s;
  _tvpi_canonicalize_cons(res);
  return (lincons_t)res;
}

/**********************************************************************
 * Creates a linear contraint t < k (if s is true) t<=k (if s is
 * false). this one frees t and k.
 *********************************************************************/
lincons_t tvpi_create_rat_cons(linterm_t t, bool s, constant_t k)
{
  lincons_t res = _tvpi_create_rat_cons(t,s,k);
  tvpi_destroy_term(t);
  tvpi_destroy_cst(k);
  return res;
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
  mpq_init(res->coeffs[0]);
  mpq_set(res->coeffs[0],arg->coeffs[0]);
  mpq_init(res->coeffs[1]);
  mpq_set(res->coeffs[1],arg->coeffs[1]);
  res->vars[0] = arg->vars[0];
  res->vars[1] = arg->vars[1];
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
  return tvpi_negate_rat_cons(l);
}

lincons_t tvpi_negate_rat_cons(lincons_t l)
{
  lincons_t res = _tvpi_create_rat_cons(tvpi_get_term(l),!tvpi_is_strict(l),
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
  return mpq_sgn(y->coeffs[0]) < 0;
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
	  y1->vars[0], y1->vars[1], (tvpi_is_strict (l1) ? "<" : "<="), 
	  ((tvpi_cst_t*) a1)->int_val, 
	  y2->vars[0], y2->vars[1], (tvpi_is_strict (l2) ? "<" : "<="), 
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
  return tvpi_resolve_rat_cons(l1,l2,x);
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
  tvpi_term_t *x1 = (tvpi_term_t*)t1;
  linterm_t t2 = tvpi_get_term(l2);
  tvpi_term_t *x2 = (tvpi_term_t*)t2;

  //if there is no resolvent between t1 and t2
  tvpi_resolve_t resolve = _tvpi_terms_have_resolvent(x1,x2,x);
  if(!resolve.term) return NULL;

  //get the constant
  constant_t c12 = tvpi_cst_mul(c1,x2->coeffs[resolve.cst1]);
  constant_t c21 = tvpi_cst_mul(c2,x1->coeffs[resolve.cst2]);
  constant_t c3 = tvpi_cst_add(c12,c21);
  tvpi_destroy_cst(c12);      
  tvpi_destroy_cst(c21);      

  //X-Y <= C1 and Y-Z <= C2 ===> X-Z <= C1+C2
  if(!tvpi_is_strict(l1) && !tvpi_is_strict(l2)) {
    lincons_t res = tvpi_create_rat_cons(resolve.term,0,c3);
    return res;
  }

  //for all other cases, X-Z < C1+C2
  lincons_t res = tvpi_create_rat_cons(resolve.term,1,c3);
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
    cn->cons = tvpi_dup_lincons(c);
    cn->node = tdd_new_var(m,(lincons_t)c);
    //if not at the start of the list
    if(prev) {
      cn->next = prev->next;
      prev->next = cn;
    }
    //if at the start of the list
    else {
      tvpi_theory_t *theory = (tvpi_theory_t*)m->theory;
      cn->next = theory->cons_node_map[c->term->vars[0]][c->term->vars[1]];
      theory->cons_node_map[c->term->vars[0]][c->term->vars[1]] = cn;
    }
    return cn->node;
  }

  //if i found a matching element, return it
  if(tvpi_term_equals(curr->cons->term,c->term) &&
     ((tvpi_is_strict(curr->cons) && tvpi_is_strict(c)) ||
      (!tvpi_is_strict(curr->cons) && !tvpi_is_strict(c))) &&
     tvpi_cst_eq(curr->cons->cst,c->cst)) return curr->node;

  //if the c implies curr, then add c just before curr
  if(m->theory->is_stronger_cons(c,curr->cons)) {
    tvpi_cons_node_t *cn = 
      (tvpi_cons_node_t*)malloc(sizeof(tvpi_cons_node_t));
    cn->cons = tvpi_dup_lincons(c);
    cn->node = tdd_new_var_before(m,curr->node,(lincons_t)c);
    //if not at the start of the list
    if(prev) {
      cn->next = prev->next;
      prev->next = cn;
    }
    //if at the start of the list
    else {
      tvpi_theory_t *theory = (tvpi_theory_t*)m->theory;
      cn->next = theory->cons_node_map[c->term->vars[0]][c->term->vars[1]];
      theory->cons_node_map[c->term->vars[0]][c->term->vars[1]] = cn;
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
    tvpi_get_node(m,theory->cons_node_map[c->term->vars[0]][c->term->vars[1]],NULL,c);

  //cleanup
  if(neg) {
    res = tdd_not(res);
    tvpi_destroy_lincons(l);
  }
  
  //all done
  return res;
}

/**********************************************************************
 * print a constraint - this one takes a linconst_t as input
 *********************************************************************/
void tvpi_print_lincons(FILE *f,lincons_t l)
{
  tvpi_print_cons(f,(tvpi_cons_t*)l);
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
  res->base.term_has_vars = tvpi_term_has_vars;
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
  res->base.print_lincons = tvpi_print_lincons;  
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
  return tvpi_create_rat_theory(vn);
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
        tvpi_destroy_lincons(curr->cons);
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

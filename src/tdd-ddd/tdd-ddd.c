/**********************************************************************
 * The main file that provides the DDD theory.
 *********************************************************************/


#include "tdd-dddInt.h"

static void check_theory_level_consistency (tdd_manager*);

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
 * create -1*c in place
 *********************************************************************/
void ddd_negate_cst_inplace (ddd_cst_t *c)
{
  switch(c->type)
    {
    case DDD_INT:
      if(c->int_val == INT_MAX) c->int_val = INT_MIN;
      else if(c->int_val == INT_MIN) c->int_val = INT_MAX;
      else c->int_val = -(c->int_val);
      break;
    case DDD_RAT:
      if(c->rat_val.quot == INT_MAX) {
        c->rat_val.quot = INT_MIN;
        c->rat_val.rem = 1;
      } else if(c->rat_val.quot == INT_MIN) {
        c->rat_val.quot = INT_MAX;
        c->rat_val.rem = 1;
      } else c->rat_val.quot = -(c->rat_val.quot);
      break;
    case DDD_DBL:
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
constant_t ddd_negate_cst (constant_t c)
{
  ddd_cst_t *x = ddd_dup_cst((ddd_cst_t*)c);
  ddd_negate_cst_inplace(x);
  return (constant_t)x;
}

/**
 * Returns c1 + c2. Allocates a new constant.
 */
constant_t ddd_add_int_cst (constant_t c1, constant_t c2)
{
  ddd_cst_t *x1 = ddd_dup_cst ((ddd_cst_t*)c1);
  ddd_cst_t *x2 = (ddd_cst_t*)c2;
  

  assert (x1->type == DDD_INT && x2->type == DDD_INT);

  /* XXX Should check for overflow */
  x1->int_val += x2->int_val;
  return (constant_t)x1;

}

/**
 * Returns c1 * c2. Allocates a new constant 
 */
constant_t ddd_mul_int_cst (constant_t c1, constant_t c2)
{
  ddd_cst_t *x1 = ddd_dup_cst ((ddd_cst_t*)c1);
  ddd_cst_t *x2 = (ddd_cst_t*)c2;
  
  assert (x1->type == DDD_INT && x2->type == DDD_INT);
  
  /** XXX Check for overflow */
  x1->int_val *= x2->int_val;
  return (constant_t)x1;
}




/**********************************************************************
 * Compares c1 and c2 for =
 * Returns true if c1 and c2 are of same type and c1 = c2
 * Returns false otherwise
 *********************************************************************/
bool ddd_cst_eq (constant_t c1,constant_t c2)
{
  ddd_cst_t *x1 = (ddd_cst_t*)c1;
  ddd_cst_t *x2 = (ddd_cst_t*)c2;

  if(x1->type != x2->type) return 0;

  switch(x1->type)
    {
    case DDD_INT:
      return (x1->int_val == x2->int_val);
    case DDD_RAT:
      if(ddd_is_pinf_cst(c1)) return ddd_is_pinf_cst(c2);
      if(ddd_is_ninf_cst(c1)) return ddd_is_ninf_cst(c2);
      if(ddd_is_pinf_cst(c2)) return ddd_is_pinf_cst(c1);
      if(ddd_is_ninf_cst(c2)) return ddd_is_ninf_cst(c1);
      return (x1->rat_val.quot * 1.0 / x1->rat_val.rem == 
              x2->rat_val.quot * 1.0 / x2->rat_val.rem);
    case DDD_DBL:
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
      return (x1->rat_val.quot * 1.0 / x1->rat_val.rem < 
              x2->rat_val.quot * 1.0 / x2->rat_val.rem);
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
      return (x1->rat_val.quot * 1.0 / x1->rat_val.rem <= 
              x2->rat_val.quot * 1.0 / x2->rat_val.rem);
    case DDD_DBL:
      return (x1->dbl_val <= x2->dbl_val);
    default:
      return 0;
    }
}

/**********************************************************************
 * Return c1 + c2. If c1 and c2 are not of same type, return NULL.
 *********************************************************************/
constant_t ddd_cst_add(constant_t c1,constant_t c2)
{
  ddd_cst_t *x1 = (ddd_cst_t*)c1;
  ddd_cst_t *x2 = (ddd_cst_t*)c2;

  if(x1->type != x2->type) return NULL;

  switch(x1->type)
    {
    case DDD_INT:
      return ddd_create_int_cst(x1->int_val + x2->int_val);
    case DDD_RAT:
      return ddd_create_rat_cst(x1->rat_val.quot * x2->rat_val.rem + 
                                x2->rat_val.quot * x1->rat_val.rem,
                                x1->rat_val.rem * x2->rat_val.rem);
    case DDD_DBL:
      return ddd_create_double_cst(x1->dbl_val + x2->dbl_val);
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


bool 
ddd_sgn_cst (ddd_cst_t *c)
{
  switch (c->type)
    {
    case DDD_INT:
      return c->int_val < 0 ? -1 : (c->int_val > 0 ? 1 : 0);
    default:
      assert (0);
    }
  return 0;
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
 * Returns true if variable var has a non-zero coefficient in t
 *********************************************************************/
bool ddd_term_has_var (linterm_t t, int var)
{
  ddd_term_t *x = (ddd_term_t*)t;
  return x->var1 == var || x->var2 == var;
}

/**********************************************************************
 * Returns true if there exists a variable v in the set var whose
 * coefficient in t is non-zero.

 * t is a term, var is represented as an array of booleans, and n is
 * the size of var.
 *********************************************************************/
bool ddd_term_has_vars (linterm_t t,bool *vars)
{
  ddd_term_t *x = (ddd_term_t*)t;
  return vars[x->var1] || vars[x->var2];
}

void ddd_var_occurrences (lincons_t l, int *occurs)
{
  ddd_cons_t *cons = (ddd_cons_t*) l;
  occurs [cons->term.var1]++;
  occurs [cons->term.var2]++;
}


/**********************************************************************
 * Returns the number of variables of the theory
 *********************************************************************/
size_t ddd_num_of_vars(theory_t* self)
{
  return ((ddd_theory_t*)self)->var_num;
}

/**********************************************************************
 * Create a term given its two variables. This is a private function.
 *********************************************************************/
linterm_t _ddd_create_linterm(int v1,int v2)
{
  ddd_term_t *res = (ddd_term_t*)malloc(sizeof(ddd_term_t));
  res->var1 = v1;
  res->var2 = v2;
  return (linterm_t)res;
}

/**********************************************************************
 * print a constant
 *********************************************************************/
void ddd_print_cst(FILE *f,ddd_cst_t *c)
{
  switch(c->type) {
  case DDD_INT:
    fprintf(f,"%d",c->int_val);
    break;
  case DDD_RAT:
    fprintf(f,"%d/%d",c->rat_val.quot,c->rat_val.rem);
    break;
  case DDD_DBL:
    fprintf(f,"%lf",c->dbl_val);
    break;
  default:
    break;
  }
}

/**********************************************************************
 * print a term
 *********************************************************************/
void ddd_print_term(FILE *f,ddd_term_t *t)
{
  fprintf(f,"x%d-x%d",t->var1,t->var2);
}

/**********************************************************************
 * print a constraint - this one takes a ddd_cons_t* as input
 *********************************************************************/
void ddd_print_cons(FILE *f,ddd_cons_t *l)
{
  ddd_print_term(f,&(l->term));
  fprintf(f," %s ",l->strict ? "<" : "<=");
  ddd_print_cst(f,&(l->cst));
}

/**********************************************************************
 * Return the result of resolving t1 and t2. If the resolvant does not
 * exist, return NULL.
 *********************************************************************/
linterm_t _ddd_terms_have_resolvent(linterm_t t1, linterm_t t2, int x)
{
  ddd_term_t *x1 = (ddd_term_t*)t1;
  ddd_term_t *x2 = (ddd_term_t*)t2;
  //X-Y and Y-Z
  if(x1->var2 == x2->var1 && x1->var2 == x && x1->var1 != x2->var2) {
    return _ddd_create_linterm(x1->var1,x2->var2);
  }
  //Y-Z and X-Y
  if(x1->var1 == x2->var2 && x1->var1 == x && x1->var2 != x1->var1) {
    return _ddd_create_linterm(x2->var1,x1->var2);
  }
  //no resolvent
  return NULL;
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
  //X-Y and Y-Z OR Y-Z and X-Y
  if((x1->var2 == x2->var1 && x1->var2 == x && x1->var1 != x2->var2) || 
     (x1->var1 == x2->var2 && x1->var1 == x && x1->var2 != x2->var1)) return 1;
  //Y-Z and Y-X OR X-Y and Z-Y
  if((x1->var1 == x2->var1 && x1->var1 == x && x1->var2 != x2->var2) ||
     (x1->var2 == x2->var2 && x1->var2 == x && x1->var1 != x2->var1)) return -1;
  //no resolvant
  return 0;
}

/**********************************************************************
 * create -1*t in place -- swaps the two variables
 *********************************************************************/
void ddd_negate_term_inplace(ddd_term_t *t)
{
  t->var1 ^= t->var2;
  t->var2 = t->var1 ^ t->var2;
  t->var1 = t->var1 ^ t->var2;
}

/**********************************************************************
 * return -1*t
 *********************************************************************/
linterm_t ddd_negate_term(linterm_t t)
{
  ddd_term_t *x = ddd_dup_term((ddd_term_t*)t);
  ddd_negate_term_inplace(x);
  return (linterm_t)x;
}

/**********************************************************************
 * Returns a variable that has a non-zero coefficient in t. Returns <0
 * if no such variable exists.
 *********************************************************************/
int ddd_pick_var (linterm_t t, bool* vars)
{
  ddd_term_t *x = (ddd_term_t*)t;
  if(vars[x->var1]) return x->var1;
  if(vars[x->var2]) return x->var2;
  return -1;
}

/**********************************************************************
 * reclaim resources allocated by t
 *********************************************************************/
void ddd_destroy_term(linterm_t t)
{
  free((ddd_term_t*)t);
}

/**********************************************************************
 * Creates a linear contraint t < k (if s is true) t<=k (if s is
 * false). this one does not free t and k.
 *********************************************************************/
lincons_t _ddd_create_int_cons(linterm_t t, bool s, constant_t k)
{
  ddd_cons_t *res = (ddd_cons_t*)malloc(sizeof(ddd_cons_t));
  res->term = *((ddd_term_t*)t);

  res->cst = *((ddd_cst_t*)k);

  /* convert '<' inequalities to '<=' */
  if (s && !ddd_is_pinf_cst(&(res->cst)) && !ddd_is_ninf_cst(&(res->cst)))
    res->cst.int_val--;

  /* all integer constraints are non-strict */
  res->strict = 0;

  return (lincons_t)res;
}

/**********************************************************************
 * Creates a linear contraint t < k (if s is true) t<=k (if s is
 * false). this one frees t and k.
 *********************************************************************/
lincons_t ddd_create_int_cons(linterm_t t, bool s, constant_t k)
{
  lincons_t res = _ddd_create_int_cons(t,s,k);
  ddd_destroy_term(t);
  ddd_destroy_cst(k);
  return res;
}

/**********************************************************************
 * Creates a linear contraint t < k (if s is true) t<=k (if s is
 * false). this one does not free t and k.
 *********************************************************************/
lincons_t _ddd_create_rat_cons(linterm_t t, bool s, constant_t k)
{
  ddd_cons_t *res = (ddd_cons_t*)malloc(sizeof(ddd_cons_t));
  res->term = *((ddd_term_t*)t);
  res->cst = *((ddd_cst_t*)k);
  res->strict = s;
  return (lincons_t)res;
}

/**********************************************************************
 * Creates a linear contraint t < k (if s is true) t<=k (if s is
 * false). this one frees t and k.
 *********************************************************************/
lincons_t ddd_create_rat_cons(linterm_t t, bool s, constant_t k)
{
  lincons_t res = _ddd_create_rat_cons(t,s,k);
  ddd_destroy_term(t);
  ddd_destroy_cst(k);
  return res;
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
 * duplicate a term. this is a private function.
 *********************************************************************/
ddd_term_t *ddd_dup_term(ddd_term_t *arg)
{
  ddd_term_t *res = (ddd_term_t*)malloc(sizeof(ddd_term_t));
  *res = *arg;
  return res;
}

/**
 * External interface to duplicate terms 
 */
linterm_t ddd_dup_term_external (linterm_t t)
{
  return (linterm_t) (ddd_dup_term ((ddd_term_t*)t));
}


/**********************************************************************
 * get the term corresponding to the argument constraint -- the
 * returned value should NEVER be freed by the user.
 *********************************************************************/
linterm_t ddd_get_term(lincons_t l)
{
  ddd_cons_t *x = (ddd_cons_t*)l;  
  return (linterm_t)(&(x->term));
}

/**********************************************************************
 * duplicate a constant. this is a private function.
 *********************************************************************/
ddd_cst_t *ddd_dup_cst(ddd_cst_t *arg)
{
  ddd_cst_t *res = (ddd_cst_t*)malloc(sizeof(ddd_cst_t));
  *res = *arg;
  return res;
}


constant_t ddd_dup_cst_external (constant_t c)
{
  return (constant_t) (ddd_dup_cst ((ddd_cst_t*)c));
}


/**********************************************************************
 * get the constant corresponding to the argument constraint -- the
 * returned value should NEVER be freed by the user.
 *********************************************************************/
constant_t ddd_get_constant(lincons_t l)
{
  ddd_cons_t *x = (ddd_cons_t*)l;  
  return (constant_t)(&(x->cst));
}

/**********************************************************************
 * Complements a linear constraint
 *********************************************************************/
lincons_t ddd_negate_int_cons(lincons_t l)
{
  ddd_term_t t = *((ddd_term_t*)ddd_get_term(l));
  ddd_negate_term_inplace(&t);
  ddd_cst_t c = *((ddd_cst_t*)ddd_get_constant(l));
  ddd_negate_cst_inplace(&c);
  lincons_t res = _ddd_create_int_cons(&t,!ddd_is_strict(l),&c);
  return res;
}

lincons_t ddd_negate_rat_cons(lincons_t l)
{
  ddd_term_t t = *((ddd_term_t*)ddd_get_term(l));
  ddd_negate_term_inplace(&t);
  ddd_cst_t c = *((ddd_cst_t*)ddd_get_constant(l));
  ddd_negate_cst_inplace(&c);
  lincons_t res = _ddd_create_rat_cons(&t,!ddd_is_strict(l),&c);
  return res;
}


/**********************************************************************
 * Returns true if l is a negative constraint (i.e., the smallest
 * non-zero dimension has a negative coefficient.)
 *********************************************************************/
bool ddd_is_negative_cons(lincons_t l)
{
  linterm_t x = ddd_get_term(l);
  ddd_term_t *y = (ddd_term_t*)x;
  return (y->var2 < y->var1);
}

/**********************************************************************
 * If is_stronger_cons(l1, l2) then l1 implies l2
 *********************************************************************/
bool ddd_is_stronger_cons(lincons_t l1, lincons_t l2)
{
  //get the terms and constants
  linterm_t x1 = ddd_get_term(l1);
  linterm_t x2 = ddd_get_term(l2);
  constant_t a1 = ddd_get_constant(l1);
  constant_t a2 = ddd_get_constant(l2);

#ifdef DEBUG
  ddd_term_t *y1 = (ddd_term_t*)x1;
  ddd_term_t *y2 = (ddd_term_t*)x2;
  printf ("is_stronger_cons ( x%d - x%d %s %d with x%d - x%d %s %d )\n",
	  y1->var1, y1->var2, (ddd_is_strict (l1) ? "<" : "<="), 
	  ((ddd_cst_t*) a1)->int_val, 
	  y2->var1, y2->var2, (ddd_is_strict (l2) ? "<" : "<="), 
	  ((ddd_cst_t*) a2)->int_val);
#endif

  //if the terms are different return false
  if(!ddd_term_equals(x1,x2)) return 0;

  /*
   * We assume that all integer constraints are non-strict, i.e., of
   * the form t1 <= c.
   */

  if (!ddd_is_strict (l1) && ddd_is_strict (l2))
    return ddd_cst_lt(a1, a2);
  return ddd_cst_le (a1, a2);  
}

/**********************************************************************
 * Computes the resolvent of constraints l1 and l2 from an integer
 * theory on x. Returns NULL if there is no resolvent.
 *********************************************************************/
lincons_t ddd_resolve_int_cons(lincons_t l1, lincons_t l2, int x)
{
  //get the constants
  constant_t c1 = ddd_get_constant(l1);
  constant_t c2 = ddd_get_constant(l2);

  //if any of the constants is infinity, there is no resolvant
  if(ddd_is_pinf_cst(c1) || ddd_is_ninf_cst(c1) ||
     ddd_is_pinf_cst(c2) || ddd_is_ninf_cst(c2)) return NULL;

  //get the terms
  linterm_t t1 = ddd_get_term(l1);
  linterm_t t2 = ddd_get_term(l2);

  //if there is no resolvent between t1 and t2
  linterm_t t3 = _ddd_terms_have_resolvent(t1,t2,x);
  if(!t3) return NULL; 

  /*  X-Y <= C1 and Y-Z <= C2 ===> X-Z <= C1+C2 */
  constant_t c3 = ddd_cst_add(c1,c2);
  lincons_t res = ddd_create_int_cons(t3,0,c3);
  return res;
}

/**********************************************************************
 * Computes the resolvent of constraints l1 and l2 from a rational
 * theory on x. Returns NULL if there is no resolvent.
 *********************************************************************/
lincons_t ddd_resolve_rat_cons(lincons_t l1, lincons_t l2, int x)
{
  //get the constants
  constant_t c1 = ddd_get_constant(l1);
  constant_t c2 = ddd_get_constant(l2);

  //if any of the constants is infinity, there is no resolvant
  if(ddd_is_pinf_cst(c1) || ddd_is_ninf_cst(c1) ||
     ddd_is_pinf_cst(c2) || ddd_is_ninf_cst(c2)) return NULL;

  //get the terms
  linterm_t t1 = ddd_get_term(l1);
  linterm_t t2 = ddd_get_term(l2);

  //if there is no resolvent between t1 and t2
  linterm_t t3 = _ddd_terms_have_resolvent(t1,t2,x);
  if(!t3) return NULL;

  //X-Y <= C1 and Y-Z <= C2 ===> X-Z <= C1+C2
  if(!ddd_is_strict(l1) && !ddd_is_strict(l2)) {
    constant_t c3 = ddd_cst_add(c1,c2);
    lincons_t res = ddd_create_rat_cons(t3,0,c3);
    return res;
  }

  //for all other cases, X-Z < C1+C2
  constant_t c3 = ddd_cst_add(c1,c2);
  lincons_t res = ddd_create_rat_cons(t3,1,c3);
  return res;
}
  
/**********************************************************************
 * destroy a linear constraint
 *********************************************************************/
void ddd_destroy_lincons(lincons_t l)
{
  free((ddd_cons_t*)l);
}
  
/**********************************************************************
 * copy a linear constraint
 *********************************************************************/
lincons_t ddd_dup_lincons(lincons_t l)
{
  ddd_cons_t *res = (ddd_cons_t*)malloc(sizeof(ddd_cons_t));
  *res = *((ddd_cons_t*)l);
  return (lincons_t)res;
}

/**********************************************************************
 * recursively go through a list of ddd_cons_node_t and return the
 * tdd_node* for an element whose cons matches with c. if no such node
 * exists, create one at the right spot.
 *********************************************************************/
tdd_node *ddd_get_node(tdd_manager* m,ddd_cons_node_t *curr,
                       ddd_cons_node_t *prev,ddd_cons_t *c)
{
  //if at the end of the list -- create a fresh tdd_node and insert it
  //at the end of the list
  if(curr == NULL) {
    ddd_cons_node_t *cn = 
      (ddd_cons_node_t*)malloc(sizeof(ddd_cons_node_t));
    cn->cons = *c;

    if (prev)
      /* last constraint in the list, need a node right after prev */
      cn->node = tdd_new_var_after (m, prev->node, (lincons_t) c);
    else
      /* first constraint in the list*/
      cn->node = tdd_new_var(m,(lincons_t)c);

    if (cn->node == NULL)
      {
	free (cn);
	return NULL;
      }
    cuddRef (cn->node);

    //if not at the start of the list
    if(prev) {
      cn->next = prev->next;
      prev->next = cn;
    }
    //if at the start of the list
    else {
      ddd_theory_t *theory = (ddd_theory_t*)m->theory;
      cn->next = theory->cons_node_map[c->term.var1][c->term.var2];
      theory->cons_node_map[c->term.var1][c->term.var2] = cn;
    }
    if (cn->node == NULL) printf ("NULL at 1\n");
    return cn->node;
  }

  //if i found a matching element, return it
  if(ddd_term_equals(&(curr->cons.term),&(c->term)) &&
     ((ddd_is_strict(&(curr->cons)) && ddd_is_strict(c)) ||
      (!ddd_is_strict(&(curr->cons)) && !ddd_is_strict(c))) &&
     ddd_cst_eq(&(curr->cons.cst),&(c->cst))) 
    return curr->node;


  //if the c implies curr, then add c just before curr
  if(m->theory->is_stronger_cons(c,&(curr->cons))) 
    {
      ddd_cons_node_t *cn = 
	(ddd_cons_node_t*)malloc(sizeof(ddd_cons_node_t));
      cn->cons = *c;
      cn->node = tdd_new_var_before(m,curr->node,(lincons_t)c);

      if (cn->node == NULL)
	{
	  free (cn);
	  return NULL;
	}
      /* grab a reference so that the node will not disapear */
      cuddRef (cn->node);
      
      //if not at the start of the list
      if(prev) {
	cn->next = prev->next;
	prev->next = cn;
      }
      //if at the start of the list
      else {
	ddd_theory_t *theory = (ddd_theory_t*)m->theory;
	cn->next = theory->cons_node_map[c->term.var1][c->term.var2];
	theory->cons_node_map[c->term.var1][c->term.var2] = cn;
      }
      return cn->node;
    }
  

  //try recursively with the next element
  return ddd_get_node(m,curr->next,curr,c);
}

/**********************************************************************
 * return a TDD node corresponding to l
 *********************************************************************/
tdd_node* ddd_to_tdd(tdd_manager* m, lincons_t l)
{
  ddd_theory_t *theory = (ddd_theory_t*)m->theory;

  //negate the constraint if necessary
  bool neg = theory->base.is_negative_cons(l);
  if(neg) l = theory->base.negate_cons (l);

  //convert to right type
  ddd_cons_t *c = (ddd_cons_t*)l;

  //find the right node. create one if necessary.
  tdd_node *res = 
    ddd_get_node(m,theory->cons_node_map[c->term.var1][c->term.var2],NULL,c);


  //cleanup
  if(neg) 
    ddd_destroy_lincons(l);

  //all done
  return neg && res != NULL ? tdd_not (res) : res;
}

/**********************************************************************
 * print a constraint - this one takes a linconst_t as input
 *********************************************************************/
void ddd_print_lincons(FILE *f,lincons_t l)
{
  ddd_print_cons(f,(ddd_cons_t*)l);
}


void ddd_debug_dump (tdd_manager * tdd)
{
  int i, j;
  ddd_theory_t* th = (ddd_theory_t*) tdd->theory;

  
  check_theory_level_consistency (tdd);

  for (i = 0; i < th->var_num; i++)
    for (j = i+1; j < th->var_num; j++)
      {
	if (th->cons_node_map [i][j] == NULL) continue;
	
	fprintf (stderr, "x%d-x%d: ", i, j);
	{
	  ddd_cons_node_t * node;
	  for (node = th->cons_node_map[i][j]; 
	       node != NULL; node = node->next)
	    {
	      ddd_print_cst (stderr, &(node->cons.cst));
	      if (node->cons.strict)
		fprintf (stderr, ")");
	      fprintf (stderr, " ");
	    }
	}
	fprintf (stderr, "\n");
      }
}


void check_theory_level_consistency (tdd_manager* tdd)
{
  int i, j;
  
  ddd_theory_t* t;
  DdManager *cudd;

  t = (ddd_theory_t*) (tdd->theory);
  cudd = tdd->cudd;
  
  fprintf (stderr, "CHECK_THEORY_LEVEL_CONSITENCY START\n");
  
  for (i = 0; i < t->var_num; i++)
    for (j = i + 1 ; j < t->var_num; j++)
      {
	/* expected level */
	unsigned int eLevel; 
	ddd_cons_node_t * n;

	if (t->cons_node_map [i][j] == NULL) continue;
	
	n = t->cons_node_map[i][j];
	eLevel = cuddI(cudd,(n->node->index)) + 1;
	
	while (n->next != NULL)
	  {
	    int nLevel;
	    n = n->next;
	    nLevel = cuddI (cudd, n->node->index);
	
	    assert (nLevel == eLevel);
	    
	    if (nLevel != eLevel)
	      {
		fprintf (stderr, "Ordering problem. Constraint: ");
		ddd_print_cons (stderr, &n->cons);
		fprintf (stderr, " expected level %d, actual level %d\n",
			 eLevel, nLevel);
	      }
	    eLevel = nLevel + 1;
	  }
      }
  fprintf (stderr, "CHECK_THEORY_LEVEL_CONSITENCY END\n");
}


/**********************************************************************
 * common steps when creating any theory - argument is the number of
 * variables
 *********************************************************************/
ddd_theory_t *ddd_create_theory_common(size_t vn)
{
  ddd_theory_t *res = (ddd_theory_t*)malloc(sizeof(ddd_theory_t));
  memset((void*)(res),0,sizeof(ddd_theory_t));
  res->base.create_int_cst = ddd_create_int_cst;
  res->base.create_rat_cst = ddd_create_rat_cst;
  res->base.create_double_cst = ddd_create_double_cst;
  res->base.negate_cst = ddd_negate_cst;
  res->base.dup_cst = ddd_dup_cst_external;
  res->base.is_pinf_cst = ddd_is_pinf_cst;
  res->base.is_ninf_cst = ddd_is_ninf_cst;
  res->base.sgn_cst = (int(*)(constant_t))ddd_sgn_cst;
  res->base.destroy_cst = ddd_destroy_cst;
  res->base.create_linterm = ddd_create_linterm;
  res->base.dup_term = ddd_dup_term_external;
  res->base.term_equals = ddd_term_equals;
  res->base.term_has_var = ddd_term_has_var;
  res->base.term_has_vars = ddd_term_has_vars;
  res->base.num_of_vars = ddd_num_of_vars;
  res->base.var_occurrences = ddd_var_occurrences;
  res->base.terms_have_resolvent = ddd_terms_have_resolvent;
  res->base.negate_term = ddd_negate_term;
  res->base.pick_var = ddd_pick_var;
  res->base.destroy_term = ddd_destroy_term;
  res->base.is_strict = ddd_is_strict;
  res->base.get_term = ddd_get_term;
  res->base.get_constant = ddd_get_constant;
  res->base.is_negative_cons = ddd_is_negative_cons;
  res->base.is_stronger_cons = ddd_is_stronger_cons;
  res->base.destroy_lincons = ddd_destroy_lincons;
  res->base.dup_lincons = ddd_dup_lincons;
  res->base.to_tdd = ddd_to_tdd;
  res->base.print_lincons = ddd_print_lincons;  
  res->base.theory_debug_dump = ddd_debug_dump;
  res->base.qelim_init = ddd_qelim_init;
  res->base.qelim_push = ddd_qelim_push;
  res->base.qelim_pop = ddd_qelim_pop;
  res->base.qelim_solve = ddd_qelim_solve;
  res->base.qelim_destroy_context = ddd_qelim_destroy_context;
  res->var_num = vn;
  //create maps from constraints to DD nodes -- one per variable pair
  res->cons_node_map = (ddd_cons_node_t ***)malloc(vn * sizeof(ddd_cons_node_t **));
  size_t i = 0;
  for(;i < vn;++i) {
    res->cons_node_map[i] = (ddd_cons_node_t **)malloc(vn * sizeof(ddd_cons_node_t *));
    size_t j = 0;
    for(;j < vn;++j) res->cons_node_map[i][j] = NULL;
  }
  return res;
}

/**********************************************************************
 * create a DDD theory of integers - the argument is the number of
 * variables
 *********************************************************************/
theory_t *ddd_create_int_theory(size_t vn)
{
  ddd_theory_t *res = ddd_create_theory_common(vn);

  res->base.add_cst = ddd_add_int_cst;
  res->base.mul_cst = ddd_mul_int_cst;
  
  res->base.create_cons = ddd_create_int_cons;
  res->base.negate_cons = ddd_negate_int_cons;
  res->base.resolve_cons = ddd_resolve_int_cons;
  res->type = DDD_INT;
  return (theory_t*)res;
}

/**********************************************************************
 * create a DDD theory of rationals - the argument is the number of
 * variables
 *********************************************************************/
theory_t *ddd_create_rat_theory(size_t vn)
{
  ddd_theory_t *res = ddd_create_theory_common(vn);
  res->base.create_cons = ddd_create_rat_cons;
  res->base.negate_cons = ddd_negate_rat_cons;
  res->base.resolve_cons = ddd_resolve_rat_cons;
  res->type = DDD_RAT;
  return (theory_t*)res;
}

/**********************************************************************
 * destroy a DDD theory
 *********************************************************************/
void ddd_destroy_theory(theory_t *t)
{
  //free the cons_node_map
  ddd_cons_node_t ***cnm = ((ddd_theory_t*)t)->cons_node_map;
  size_t vn = ((ddd_theory_t*)t)->var_num;
  size_t i = 0;
  for(;i < vn;++i) {
    size_t j = 0;
    for(;j < vn;++j) {
      ddd_cons_node_t *curr = cnm[i][j];
      while(curr) {
        ddd_cons_node_t *next = curr->next;
        free(curr);
        curr = next;
      }
    }
    free(cnm[i]);
  }
  free(cnm);

  //free the theory
  free((ddd_theory_t*)t);
}

/**********************************************************************
 * end of tdd-ddd.c
 *********************************************************************/

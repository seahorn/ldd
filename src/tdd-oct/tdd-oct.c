/**********************************************************************
 * The main file that provides the OCT theory.
 *********************************************************************/

#include "tdd-octInt.h"

/**********************************************************************
 * create an integer constant
 *********************************************************************/
constant_t oct_create_int_cst(int v)
{
  oct_cst_t *res = (oct_cst_t*)malloc(sizeof(oct_cst_t));
  res->type = OCT_INT;
  res->int_val = v;
  return (constant_t)res;
}

/**********************************************************************
 * create a rational constant. we use the div_t datatype to store the
 * numerator and denominator.
 *********************************************************************/
constant_t oct_create_rat_cst(int n,int d)
{
  oct_cst_t *res = (oct_cst_t*)malloc(sizeof(oct_cst_t));
  res->type = OCT_RAT;
  res->rat_val.quot = n;
  res->rat_val.rem = d;
  return (constant_t)res;
}

/**********************************************************************
 * create a double constant
 *********************************************************************/
constant_t oct_create_double_cst(double v)
{
  oct_cst_t *res = (oct_cst_t*)malloc(sizeof(oct_cst_t));
  res->type = OCT_DBL;
  res->dbl_val = v;
  return (constant_t)res;
}

/**********************************************************************
 * create -1*c in place
 *********************************************************************/
void oct_negate_cst_inplace (oct_cst_t *c)
{
  switch(c->type)
    {
    case OCT_INT:
      if(c->int_val == INT_MAX) c->int_val = INT_MIN;
      else if(c->int_val == INT_MIN) c->int_val = INT_MAX;
      else c->int_val = -(c->int_val);
      break;
    case OCT_RAT:
      if(c->rat_val.quot == INT_MAX) {
        c->rat_val.quot = INT_MIN;
        c->rat_val.rem = 1;
      } else if(c->rat_val.quot == INT_MIN) {
        c->rat_val.quot = INT_MAX;
        c->rat_val.rem = 1;
      } else c->rat_val.quot = -(c->rat_val.quot);
      break;
    case OCT_DBL:
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
constant_t oct_negate_cst (constant_t c)
{
  oct_cst_t *x = dup_cst((oct_cst_t*)c);
  oct_negate_cst_inplace(x);
  return (constant_t)x;
}

/**********************************************************************
 * Compares c1 and c2 for =
 * Returns true if c1 and c2 are of same type and c1 = c2
 * Returns false otherwise
 *********************************************************************/
bool oct_cst_eq (constant_t c1,constant_t c2)
{
  oct_cst_t *x1 = (oct_cst_t*)c1;
  oct_cst_t *x2 = (oct_cst_t*)c2;

  if(x1->type != x2->type) return 0;

  switch(x1->type)
    {
    case OCT_INT:
      return (x1->int_val == x2->int_val);
    case OCT_RAT:
      if(oct_is_pinf_cst(c1)) return oct_is_pinf_cst(c2);
      if(oct_is_ninf_cst(c1)) return oct_is_ninf_cst(c2);
      if(oct_is_pinf_cst(c2)) return oct_is_pinf_cst(c1);
      if(oct_is_ninf_cst(c2)) return oct_is_ninf_cst(c1);
      return (x1->rat_val.quot * 1.0 / x1->rat_val.rem == 
              x2->rat_val.quot * 1.0 / x2->rat_val.rem);
    case OCT_DBL:
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
bool oct_cst_lt (constant_t c1,constant_t c2)
{
  oct_cst_t *x1 = (oct_cst_t*)c1;
  oct_cst_t *x2 = (oct_cst_t*)c2;

  if(x1->type != x2->type) return 0;

  switch(x1->type)
    {
    case OCT_INT:
      return (x1->int_val < x2->int_val);
    case OCT_RAT:
      if(oct_is_pinf_cst(c1)) return 0;
      if(oct_is_pinf_cst(c2)) return !oct_is_pinf_cst(c1);
      if(oct_is_ninf_cst(c1)) return !oct_is_ninf_cst(c2);
      if(oct_is_ninf_cst(c2)) return 0;
      return (x1->rat_val.quot * 1.0 / x1->rat_val.rem < 
              x2->rat_val.quot * 1.0 / x2->rat_val.rem);
    case OCT_DBL:
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
bool oct_cst_le (constant_t c1,constant_t c2)
{
  oct_cst_t *x1 = (oct_cst_t*)c1;
  oct_cst_t *x2 = (oct_cst_t*)c2;

  if(x1->type != x2->type) return 0;

  switch(x1->type)
    {
    case OCT_INT:
      return (x1->int_val <= x2->int_val);
    case OCT_RAT:
      if(oct_is_pinf_cst(c1)) return oct_is_pinf_cst(c2);
      if(oct_is_pinf_cst(c2)) return 1;
      if(oct_is_ninf_cst(c1)) return 1;
      if(oct_is_ninf_cst(c2)) return oct_is_ninf_cst(c1);
      return (x1->rat_val.quot * 1.0 / x1->rat_val.rem <= 
              x2->rat_val.quot * 1.0 / x2->rat_val.rem);
    case OCT_DBL:
      return (x1->dbl_val <= x2->dbl_val);
    default:
      return 0;
    }
}

/**********************************************************************
 * Return c1 + c2. If c1 and c2 are not of same type, return NULL.
 *********************************************************************/
constant_t oct_cst_add(constant_t c1,constant_t c2)
{
  oct_cst_t *x1 = (oct_cst_t*)c1;
  oct_cst_t *x2 = (oct_cst_t*)c2;

  if(x1->type != x2->type) return NULL;

  switch(x1->type)
    {
    case OCT_INT:
      return oct_create_int_cst(x1->int_val + x2->int_val);
    case OCT_RAT:
      return oct_create_rat_cst(x1->rat_val.quot * x2->rat_val.rem + 
                                x2->rat_val.quot * x1->rat_val.rem,
                                x1->rat_val.rem * x2->rat_val.rem);
    case OCT_DBL:
      return oct_create_double_cst(x1->dbl_val + x2->dbl_val);
    default:
      return 0;
    }
}


/**********************************************************************
 * return true if the argument is positive infinity
 *********************************************************************/
bool oct_is_pinf_cst(constant_t c)
{
  oct_cst_t *x = (oct_cst_t*)c;
  switch(x->type)
    {
    case OCT_INT:
      return x->int_val == INT_MAX;
    case OCT_RAT:
      return (x->rat_val.quot == INT_MAX); 
    case OCT_DBL:
      return (x->dbl_val == DBL_MAX);
    default:
      return 0;
    }
}

/**********************************************************************
 * return true if the argument is negative infinity
 *********************************************************************/
bool oct_is_ninf_cst(constant_t c)
{
  oct_cst_t *x = (oct_cst_t*)c;
  switch(x->type)
    {
    case OCT_INT:
      return x->int_val == INT_MIN;
    case OCT_RAT:
      return (x->rat_val.quot == INT_MIN); 
    case OCT_DBL:
      return (x->dbl_val == DBL_MIN);
    default:
      return 0;
    }
}

/**********************************************************************
 * destroy a constant
 *********************************************************************/
void oct_destroy_cst(constant_t c)
{
  free((oct_cst_t*)c);
}

/**********************************************************************
 * Create a linear term: the first argument is an array of variable
 * coefficients. the second argument is the size of the array of
 * coefficients.
 *********************************************************************/
linterm_t oct_create_linterm(int* coeffs, size_t n)
{
  oct_term_t *res = (oct_term_t*)malloc(sizeof(oct_term_t));
  memset((void*)(res),sizeof(oct_term_t),0);
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
bool oct_term_equals(linterm_t t1, linterm_t t2)
{
  oct_term_t *x1 = (oct_term_t*)t1;
  oct_term_t *x2 = (oct_term_t*)t2;
  return (x1->coeff1 == x2->coeff1 && x1->var1 == x2->var1 && 
          x1->coeff2 == x2->coeff2 && x1->var2 == x2->var2);
}

/**********************************************************************
 * Returns true if there exists a variable v in the set var whose
 * coefficient in t is non-zero.

 * t is a term, var is represented as an array of booleans, and n is
 * the size of var.
 *********************************************************************/
bool oct_term_has_var (linterm_t t,bool *vars)
{
  oct_term_t *x = (oct_term_t*)t;
  return vars[x->var1] || vars[x->var2];
}

/**********************************************************************
 * Returns the number of variables of the theory
 *********************************************************************/
size_t oct_num_of_vars(theory_t* self)
{
  return ((oct_theory_t*)self)->var_num;
}

/**********************************************************************
 * Create a term given its two variables. This is a private function.
 *********************************************************************/
linterm_t _oct_create_linterm(int cf1,int v1,int cf2,int v2)
{
  oct_term_t *res = (oct_term_t*)malloc(sizeof(oct_term_t));
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
linterm_t _oct_terms_have_resolvent(linterm_t t1, linterm_t t2, int x)
{
  oct_term_t *x1 = (oct_term_t*)t1;
  oct_term_t *x2 = (oct_term_t*)t2;
  //first and first variables cancel
  if(x1->var1 == x2->var1 && x1->var1 == x && 
     x1->coeff1 == -(x2->coeff1) && x1->var2 != x2->var2) {
    return _oct_create_linterm(x1->coeff2,x1->var2,x2->coeff2,x2->var2);
  }
  //first and second variables cancel
  if(x1->var1 == x2->var2 && x1->var1 == x && 
     x1->coeff1 == -(x2->coeff2) && x1->var2 != x2->var1) {
    return _oct_create_linterm(x1->coeff2,x1->var2,x2->coeff1,x2->var1);
  }
  //second and first variables cancel
  if(x1->var2 == x2->var1 && x1->var2 == x && 
     x1->coeff2 == -(x2->coeff1) && x1->var1 != x2->var2) {
    return _oct_create_linterm(x1->coeff1,x1->var1,x2->coeff2,x2->var2);
  }
  //second and second variables cancel
  if(x1->var2 == x2->var2 && x1->var2 == x && 
     x1->coeff2 == -(x2->coeff2) && x1->var1 != x2->var1) {
    return _oct_create_linterm(x1->coeff1,x1->var1,x2->coeff1,x2->var1);
  }
  //no resolvent
  return NULL;
}



/**********************************************************************
 * Returns >0 if t1 and t2 have a resolvent on variable x, 
 * Returns <0 if t1 and -t2 have a resolvent on variable x
 * Return 0 if t1 and t2 do not resolve.
 *********************************************************************/
int oct_terms_have_resolvent(linterm_t t1, linterm_t t2, int x)
{
  oct_term_t *x1 = (oct_term_t*)t1;
  oct_term_t *x2 = (oct_term_t*)t2;
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
void oct_negate_term_inplace(oct_term_t *t)
{
  t->coeff1 = -(t->coeff1);
  t->coeff2 = -(t->coeff2);
}

/**********************************************************************
 * return -1*t
 *********************************************************************/
linterm_t oct_negate_term(linterm_t t)
{
  oct_term_t *x = dup_term((oct_term_t*)t);
  oct_negate_term_inplace(x);
  return (linterm_t)x;
}

/**********************************************************************
 * Returns a variable that has a non-zero coefficient in t. Returns <0
 * if no such variable exists.
 *********************************************************************/
int oct_pick_var (linterm_t t, bool* vars)
{
  oct_term_t *x = (oct_term_t*)t;
  if(vars[x->var1]) return x->var1;
  if(vars[x->var2]) return x->var2;
  return -1;
}

/**********************************************************************
 * reclaim resources allocated by t
 *********************************************************************/
void oct_destroy_term(linterm_t t)
{
  free((oct_term_t*)t);
}

/**********************************************************************
 * Creates a linear contraint t < k (if s is true) t<=k (if s is false)
 *********************************************************************/
lincons_t oct_create_rat_cons(linterm_t t, bool s, constant_t k)
{
  oct_cons_t *res = (oct_cons_t*)malloc(sizeof(oct_cons_t));
  res->term = *((oct_term_t*)t);
  res->cst = *((oct_cst_t*)k);
  res->strict = s;
  return (lincons_t)res;
}

/**********************************************************************
 * Creates a linear contraint t < k (if s is true) t<=k (if s is false)
 *********************************************************************/
lincons_t oct_create_int_cons(linterm_t t, bool s, constant_t k)
{
  oct_cons_t *res = (oct_cons_t*)malloc(sizeof(oct_cons_t));
  res->term = *((oct_term_t*)t);

  res->cst = *((oct_cst_t*)k);

  /* convert '<' inequalities to '<=' */
  if (s && !oct_is_pinf_cst(&(res->cst)) && !oct_is_ninf_cst(&(res->cst)))
    res->cst.int_val--;

  /* all integer constraints are non-strict */
  res->strict = 0;

  return (lincons_t)res;
}


/**********************************************************************
 * Returns true if l is a strict constraint
 *********************************************************************/
bool oct_is_strict(lincons_t l)
{
  oct_cons_t *x = (oct_cons_t*)l;
  return x->strict;
}

/**********************************************************************
 * duplicate a term. this is a private function.
 *********************************************************************/
oct_term_t *dup_term(oct_term_t *arg)
{
  oct_term_t *res = (oct_term_t*)malloc(sizeof(oct_term_t));
  *res = *arg;
  return res;
}

/**********************************************************************
 * get the term corresponding to the argument constraint -- the
 * returned value should NEVER be freed by the user.
 *********************************************************************/
linterm_t oct_get_term(lincons_t l)
{
  oct_cons_t *x = (oct_cons_t*)l;  
  return (linterm_t)(&(x->term));
}

/**********************************************************************
 * duplicate a constant. this is a private function.
 *********************************************************************/
oct_cst_t *dup_cst(oct_cst_t *arg)
{
  oct_cst_t *res = (oct_cst_t*)malloc(sizeof(oct_cst_t));
  *res = *arg;
  return res;
}

/**********************************************************************
 * get the constant corresponding to the argument constraint -- the
 * returned value should NEVER be freed by the user.
 *********************************************************************/
constant_t oct_get_constant(lincons_t l)
{
  oct_cons_t *x = (oct_cons_t*)l;  
  return (constant_t)(&(x->cst));
}

/**********************************************************************
 * Complements a linear constraint
 *********************************************************************/
lincons_t oct_negate_int_cons(lincons_t l)
{
  oct_term_t t = *((oct_term_t*)oct_get_term(l));
  oct_negate_term_inplace(&t);
  oct_cst_t c = *((oct_cst_t*)oct_get_constant(l));
  oct_negate_cst_inplace(&c);
  lincons_t res = oct_create_int_cons(&t,!oct_is_strict(l),&c);
  return res;
}

lincons_t oct_negate_rat_cons(lincons_t l)
{
  oct_term_t t = *((oct_term_t*)oct_get_term(l));
  oct_negate_term_inplace(&t);
  oct_cst_t c = *((oct_cst_t*)oct_get_constant(l));
  oct_negate_cst_inplace(&c);
  lincons_t res = oct_create_rat_cons(&t,!oct_is_strict(l),&c);
  return res;
}


/**********************************************************************
 * Returns true if l is a negative constraint (i.e., the smallest
 * non-zero dimension has a negative coefficient.)
 *********************************************************************/
bool oct_is_negative_cons(lincons_t l)
{
  linterm_t x = oct_get_term(l);
  oct_term_t *y = (oct_term_t*)x;
  bool res = (y->coeff1 == -1);
  return res;
}

/**********************************************************************
 * If is_stronger_cons(l1, l2) then l1 implies l2
 *********************************************************************/
bool oct_is_stronger_cons(lincons_t l1, lincons_t l2)
{
  //get the terms and constants
  linterm_t x1 = oct_get_term(l1);
  linterm_t x2 = oct_get_term(l2);
  oct_term_t *y1 = (oct_term_t*)x1;
  oct_term_t *y2 = (oct_term_t*)x2;
  constant_t a1 = oct_get_constant(l1);
  constant_t a2 = oct_get_constant(l2);

#ifdef DEBUG
  printf ("is_stronger_cons ( x%d - x%d %s %d with x%d - x%d %s %d )\n",
	  y1->var1, y1->var2, (oct_is_strict (l1) ? "<" : "<="), 
	  ((oct_cst_t*) a1)->int_val, 
	  y2->var1, y2->var2, (oct_is_strict (l2) ? "<" : "<="), 
	  ((oct_cst_t*) a2)->int_val);
#endif

  //if the two terms are not both of the form X-Y return false
  if(y1->var1 != y2->var1 || y1->var2 != y2->var2) return 0;

  /*
   * We assume that all integer constraints are non-strict, i.e., of
   * the form t1 <= c.
   */

  if (!oct_is_strict (l1) && oct_is_strict (l2))
    return oct_cst_lt(a1, a2);
  return oct_cst_le (a1, a2);  
}


/**********************************************************************
 * Computes the resolvent of l1 and l2 on x. Returns NULL if there is
 * no resolvent.
 *********************************************************************/
lincons_t oct_resolve_int_cons(lincons_t l1, lincons_t l2, int x)
{
  //get the constants
  constant_t c1 = oct_get_constant(l1);
  constant_t c2 = oct_get_constant(l2);

  //if any of the constants is infinity, there is no resolvant
  if(oct_is_pinf_cst(c1) || oct_is_ninf_cst(c1) ||
     oct_is_pinf_cst(c2) || oct_is_ninf_cst(c2)) return NULL;

  //get the terms
  linterm_t t1 = oct_get_term(l1);
  linterm_t t2 = oct_get_term(l2);

  //if there is no resolvent between t1 and t2
  linterm_t t3 = _oct_terms_have_resolvent(t1,t2,x);
  if(!t3) return NULL; 

  /*  X-Y <= C1 and Y-Z <= C2 ===> X-Z <= C1+C2 */
  constant_t c3 = oct_cst_add(c1,c2);
  lincons_t res = oct_create_int_cons(t3,0,c3);
  oct_destroy_term(t3);
  oct_destroy_cst(c3);      
  return res;
}

lincons_t oct_resolve_rat_cons(lincons_t l1, lincons_t l2, int x)
{
  //get the constants
  constant_t c1 = oct_get_constant(l1);
  constant_t c2 = oct_get_constant(l2);

  //if any of the constants is infinity, there is no resolvant
  if(oct_is_pinf_cst(c1) || oct_is_ninf_cst(c1) ||
     oct_is_pinf_cst(c2) || oct_is_ninf_cst(c2)) return NULL;

  //get the terms
  linterm_t t1 = oct_get_term(l1);
  linterm_t t2 = oct_get_term(l2);

  //if there is no resolvent between t1 and t2
  linterm_t t3 = _oct_terms_have_resolvent(t1,t2,x);
  if(!t3) return NULL;

  //X-Y <= C1 and Y-Z <= C2 ===> X-Z <= C1+C2
  if(!oct_is_strict(l1) && !oct_is_strict(l2)) {
    constant_t c3 = oct_cst_add(c1,c2);
    lincons_t res = oct_create_rat_cons(t3,0,c3);
    oct_destroy_term(t3);
    oct_destroy_cst(c3);
    return res;
  }

  //for all other cases, X-Z < C1+C2
  constant_t c3 = oct_cst_add(c1,c2);
  lincons_t res = oct_create_rat_cons(t3,1,c3);
  oct_destroy_term(t3);
  oct_destroy_cst(c3);
  return res;
}
  
/**********************************************************************
 * destroy a linear constraint
 *********************************************************************/
void oct_destroy_lincons(lincons_t l)
{
  free((oct_cons_t*)l);
}
  
/**********************************************************************
 * copy a linear constraint
 *********************************************************************/
lincons_t oct_dup_lincons(lincons_t l)
{
  oct_cons_t *res = (oct_cons_t*)malloc(sizeof(oct_cons_t));
  *res = *((oct_cons_t*)l);
  return (lincons_t)res;
}

/**********************************************************************
 * recursively go through a list of oct_cons_node_t and return the
 * tdd_node* for an element whose cons matches with c. if no such node
 * exists, create one at the right spot.
 *********************************************************************/
tdd_node *oct_get_node(tdd_manager* m,oct_cons_node_t *curr,
                       oct_cons_node_t *prev,oct_cons_t *c)
{
  //if at the end of the list -- create a fresh tdd_node and insert it
  //at the end of the list
  if(curr == NULL) {
    oct_cons_node_t *cn = 
      (oct_cons_node_t*)malloc(sizeof(oct_cons_node_t));
    cn->cons = *c;
    cn->node = tdd_new_var(m,(lincons_t)c);
    //if not at the start of the list
    if(prev) {
      cn->next = prev->next;
      prev->next = cn;
    }
    //if at the start of the list
    else {
      oct_theory_t *theory = (oct_theory_t*)m->theory;
      cn->next = theory->cons_node_map[c->term.var1][c->term.var2];
      theory->cons_node_map[c->term.var1][c->term.var2] = cn;
    }
    return cn->node;
  }

  //if i found a matching element, return it
  if(oct_term_equals(&(curr->cons.term),&(c->term)) &&
     ((oct_is_strict(&(curr->cons)) && oct_is_strict(c)) ||
      (!oct_is_strict(&(curr->cons)) && !oct_is_strict(c))) &&
     oct_cst_eq(&(curr->cons.cst),&(c->cst))) return curr->node;

  //if the c implies curr, then add c just before curr
  if(m->theory->is_stronger_cons(c,&(curr->cons))) {
    oct_cons_node_t *cn = 
      (oct_cons_node_t*)malloc(sizeof(oct_cons_node_t));
    cn->cons = *c;
    cn->node = tdd_new_var_before(m,curr->node,(lincons_t)c);
    //if not at the start of the list
    if(prev) {
      cn->next = prev->next;
      prev->next = cn;
    }
    //if at the start of the list
    else {
      oct_theory_t *theory = (oct_theory_t*)m->theory;
      cn->next = theory->cons_node_map[c->term.var1][c->term.var2];
      theory->cons_node_map[c->term.var1][c->term.var2] = cn;
    }
    return cn->node;
  }

  //try recursively with the next element
  return oct_get_node(m,curr->next,curr,c);
}

/**********************************************************************
 * return a TDD node corresponding to l
 *********************************************************************/
tdd_node* oct_to_tdd(tdd_manager* m, lincons_t l)
{
  oct_theory_t *theory = (oct_theory_t*)m->theory;

  //negate the constraint if necessary
  bool neg = theory->base.is_negative_cons(l);
  if(neg) l = theory->base.negate_cons (l);

  //convert to right type
  oct_cons_t *c = (oct_cons_t*)l;

  //find the right node. create one if necessary.
  tdd_node *res = 
    oct_get_node(m,theory->cons_node_map[c->term.var1][c->term.var2],NULL,c);

  //cleanup
  if(neg) {
    res = tdd_not(res);
    oct_destroy_lincons(l);
  }
  
  //all done
  return res;
}

/**********************************************************************
 * common steps when creating any theory - argument is the number of
 * variables
 *********************************************************************/
oct_theory_t *oct_create_theory_common(size_t vn)
{
  oct_theory_t *res = (oct_theory_t*)malloc(sizeof(oct_theory_t));
  memset((void*)(res),sizeof(oct_theory_t),0);
  res->base.create_int_cst = oct_create_int_cst;
  res->base.create_rat_cst = oct_create_rat_cst;
  res->base.create_double_cst = oct_create_double_cst;
  res->base.negate_cst = oct_negate_cst;
  res->base.is_pinf_cst = oct_is_pinf_cst;
  res->base.is_ninf_cst = oct_is_ninf_cst;
  res->base.destroy_cst = oct_destroy_cst;
  res->base.create_linterm = oct_create_linterm;
  res->base.term_equals = oct_term_equals;
  res->base.term_has_var = oct_term_has_var;
  res->base.num_of_vars = oct_num_of_vars;
  res->base.terms_have_resolvent = oct_terms_have_resolvent;
  res->base.negate_term = oct_negate_term;
  res->base.pick_var = oct_pick_var;
  res->base.destroy_term = oct_destroy_term;
  res->base.is_strict = oct_is_strict;
  res->base.get_term = oct_get_term;
  res->base.get_constant = oct_get_constant;
  res->base.is_negative_cons = oct_is_negative_cons;
  res->base.is_stronger_cons = oct_is_stronger_cons;
  res->base.destroy_lincons = oct_destroy_lincons;
  res->base.dup_lincons = oct_dup_lincons;
  res->base.to_tdd = oct_to_tdd;
  res->var_num = vn;
  //create maps from constraints to DD nodes -- one per variable pair
  res->cons_node_map = (oct_cons_node_t ***)malloc(vn * sizeof(oct_cons_node_t **));
  size_t i = 0;
  for(;i < vn;++i) {
    res->cons_node_map[i] = (oct_cons_node_t **)malloc(vn * sizeof(oct_cons_node_t *));
    size_t j = 0;
    for(;j < vn;++j) res->cons_node_map[i][j] = NULL;
  }
  return res;
}

/**********************************************************************
 * create a OCT theory of integers - the argument is the number of
 * variables
 *********************************************************************/
theory_t *oct_create_int_theory(size_t vn)
{
  oct_theory_t *res = oct_create_theory_common(vn);
  res->base.create_cons = oct_create_int_cons;
  res->base.negate_cons = oct_negate_int_cons;
  res->base.resolve_cons = oct_resolve_int_cons;
  res->type = OCT_INT;
  return (theory_t*)res;
}

/**********************************************************************
 * create a OCT theory of rationals - the argument is the number of
 * variables
 *********************************************************************/
theory_t *oct_create_rat_theory(size_t vn)
{
  oct_theory_t *res = oct_create_theory_common(vn);
  res->base.create_cons = oct_create_rat_cons;
  res->base.negate_cons = oct_negate_rat_cons;
  res->base.resolve_cons = oct_resolve_rat_cons;
  res->type = OCT_RAT;
  return (theory_t*)res;
}

/**********************************************************************
 * destroy a OCT theory
 *********************************************************************/
void oct_destroy_theory(theory_t *t)
{
  //free the cons_node_map
  oct_cons_node_t ***cnm = ((oct_theory_t*)t)->cons_node_map;
  size_t vn = ((oct_theory_t*)t)->var_num;
  size_t i = 0;
  for(;i < vn;++i) {
    size_t j = 0;
    for(;j < vn;++j) {
      oct_cons_node_t *curr = cnm[i][j];
      while(curr) {
        oct_cons_node_t *next = curr->next;
        free(curr);
        curr = next;
      }
    }
    free(cnm[i]);
  }
  free(cnm);

  //free the theory
  free((oct_theory_t*)t);
}

/**********************************************************************
 * end of tdd-oct.c
 *********************************************************************/

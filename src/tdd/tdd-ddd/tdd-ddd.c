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
 * if c is an integer, return c - 1, else return c
 *********************************************************************/
constant_t ddd_cst_decr(constant_t c)
{
  ddd_cst_t *x = (ddd_cst_t*)c;
  switch(x->type)
    {
    case DDD_INT:
      return ddd_is_pinf_cst(c) || ddd_is_ninf_cst(c) ? 
        (constant_t)dup_cst(x) : ddd_create_int_cst(x->int_val - 1);
    case DDD_RAT:
      return (constant_t)dup_cst(x);
    case DDD_DBL:
      return (constant_t)dup_cst(x);
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
 * Returns true if there exists a variable v in the set var whose
 * coefficient in t is non-zero.

 * t is a term, var is represented as an array of booleans, and n is
 * the size of var.
 *********************************************************************/
bool ddd_term_has_var (linterm_t t,bool *vars)
{
  ddd_term_t *x = (ddd_term_t*)t;
  return vars[x->var1] || vars[x->var2];
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
 * Returns >0 if t1 and t2 have a resolvent on variable x, 
 * Returns <0 if t1 and -t2 have a resolvent on variable x
 * Return 0 if t1 and t2 do not resolve.

 * Return the result of resolving t1 and t2 in res.
 *********************************************************************/
int _ddd_terms_have_resolvent(linterm_t t1, linterm_t t2, int x,linterm_t *res)
{
  ddd_term_t *x1 = (ddd_term_t*)t1;
  ddd_term_t *x2 = (ddd_term_t*)t2;
  //X-Y and Y-Z
  if(x1->var2 == x2->var1 && x1->var2 == x) {
    *res = _ddd_create_linterm(x1->var1,x2->var2);
    return 1;
  }
  //Y-Z and X-Y
  if(x1->var1 == x2->var2 && x1->var1 == x) {
    *res = _ddd_create_linterm(x2->var1,x1->var2);
    return 1;
  }
  //Y-Z and Y-X
  if(x1->var1 == x2->var1 && x1->var1 == x) {
    *res = _ddd_create_linterm(x2->var2,x1->var2);
    return -1;
  }
  //X-Y and Z-Y
  if(x1->var2 == x2->var2 && x1->var2 == x) {
    *res = _ddd_create_linterm(x1->var1,x2->var1);
    return -1;
  }
  //no resolvant
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
  //X-Y and Y-Z OR Y-Z and X-Y
  if((x1->var2 == x2->var1 && x1->var2 == x) || 
     (x1->var1 == x2->var2 && x1->var1 == x)) return 1;
  //Y-Z and Y-X OR X-Y and Z-Y
  if((x1->var1 == x2->var1 && x1->var1 == x) ||
     (x1->var2 == x2->var2 && x1->var2 == x)) return -1;
  //no resolvant
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
 * Returns a variable in vars that has a non-zero coefficient in
 * t. Returns <0 if no such variable exists.
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
 * duplicate a term. this is a private function.
 *********************************************************************/
ddd_term_t *dup_term(ddd_term_t *arg)
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
  return (linterm_t)dup_term(&(x->term));
}

/**********************************************************************
 * duplicate a constant. this is a private function.
 *********************************************************************/
ddd_cst_t *dup_cst(ddd_cst_t *arg)
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
  return (constant_t)dup_cst(&(x->cst));
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
 * Returns true if l is a negative constraint (i.e., the smallest
 * non-zero dimension has a negative coefficient.)
 *********************************************************************/
bool ddd_is_negative_cons(lincons_t l)
{
  linterm_t x = ddd_get_term(l);
  ddd_term_t *y = (ddd_term_t*)x;
  bool res = (y->var2 < y->var1);
  ddd_destroy_term(x);
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
      constant_t a3 = ddd_cst_decr(a2);
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
 * Computes the resolvent of l1 and l2 on x. Returns NULL if there is
 * no resolvent.
 *********************************************************************/
lincons_t ddd_resolve_cons(lincons_t l1, lincons_t l2, int x)
{
  //get the constants
  constant_t c1 = ddd_get_constant(l1);
  constant_t c2 = ddd_get_constant(l2);

  //if any of the constants is infinity, there is no resolvant
  if(ddd_is_pinf_cst(c1) || ddd_is_ninf_cst(c1) ||
     ddd_is_pinf_cst(c2) || ddd_is_ninf_cst(c2)) {
    ddd_destroy_cst(c1);
    ddd_destroy_cst(c2);
    return NULL;
  }

  //get the terms
  linterm_t t1 = ddd_get_term(l1);
  linterm_t t2 = ddd_get_term(l2);

  lincons_t res = NULL;
  linterm_t t3;

  //if there is no resolvant between t1 and t2
  if(_ddd_terms_have_resolvent(t1,t2,x,&t3) <= 0) goto DONE;

  //X-Y < C1 and Y-Z < C2 ===> X-Z < C1+(--C2). note that for
  //non-integers, -- leaves the constant unchanged. so the result is
  //X-Z < C1+C2. but for integers, the result is X-X < C1+C2-1, which
  //is what we want
  if(ddd_is_strict(l1) && ddd_is_strict(l2)) {
    constant_t c3 = ddd_cst_decr(c2);
    constant_t c4 = ddd_cst_add(c1,c3);
    ddd_destroy_cst(c3);
    res = ddd_create_cons(t3,1,c4);
    ddd_destroy_cst(c4);
  }

  //X-Y < C1 and Y-Z <= C2 ===> X-Z < C1+C2
  if((ddd_is_strict(l1) && !ddd_is_strict(l2)) ||
     (!ddd_is_strict(l1) && ddd_is_strict(l2))) {
    constant_t c3 = ddd_cst_add(c1,c2);
    res = ddd_create_cons(t3,1,c3);
    ddd_destroy_cst(c3);
  }
  //X-Y <= C1 and Y-Z <= C2 ===> X-Z <= C1+C2
  if(!ddd_is_strict(l1) && !ddd_is_strict(l2)) {
    constant_t c3 = ddd_cst_add(c1,c2);
    res = ddd_create_cons(t3,0,c3);
    ddd_destroy_cst(c3);
  }

 DONE:
  //cleanup
  ddd_destroy_cst(c1);
  ddd_destroy_cst(c2);
  ddd_destroy_term(t1);
  ddd_destroy_term(t2);
  ddd_destroy_term(t3);

  //all done
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
    cn->node = tdd_new_var(m,(lincons_t)c);
    //if not at the start of the list
    if(prev) {
      cn->next = prev->next;
      prev->next = cn;
    }
    //if at the start of the list
    else {
      ddd_theory_t *theory = (ddd_theory_t*)get_theory(m);
      cn->next = theory->cons_node_map;
      theory->cons_node_map = cn;
    }
    return cn->node;
  }

  //if i found a matching element, return it
  if(ddd_term_equals(&(curr->cons.term),&(c->term)) &&
     ddd_cst_eq(&(curr->cons.cst),&(c->cst))) return curr->node;

  //if the curr implies c, then add c just before curr
  if(ddd_is_stronger_cons(&(curr->cons),c)) {
    ddd_cons_node_t *cn = 
      (ddd_cons_node_t*)malloc(sizeof(ddd_cons_node_t));
    cn->cons = *c;
    cn->node = tdd_new_var_before(m,curr->node,(lincons_t)c);
    //if not at the start of the list
    if(prev) {
      cn->next = prev->next;
      prev->next = cn;
    }
    //if at the start of the list
    else {
      ddd_theory_t *theory = (ddd_theory_t*)get_theory(m);
      cn->next = theory->cons_node_map;
      theory->cons_node_map = cn;
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
  ddd_theory_t *theory = (ddd_theory_t*)get_theory(m);

  //negate the constraint if necessary
  bool neg = ddd_is_negative_cons(l);
  if(neg) l = ddd_negate_cons(l);

  //find the right node. create one if necessary.
  tdd_node *res = ddd_get_node(m,theory->cons_node_map,NULL,(ddd_cons_t*)l);

  //cleanup
  if(neg) ddd_destroy_lincons(l);
  //all done
  return res;
}

/**********************************************************************
 * create a DDD theory - the argument is the number of variables
 *********************************************************************/
theory_t *ddd_create_theory(ddd_type_t t,size_t vn)
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
  res->base.term_equals = ddd_term_equals;
  res->base.term_has_var = ddd_term_has_var;
  res->base.num_of_vars = ddd_num_of_vars;
  res->base.terms_have_resolvent = ddd_terms_have_resolvent;
  res->base.negate_term = ddd_negate_term;
  res->base.pick_var = ddd_pick_var;
  res->base.destroy_term = ddd_destroy_term;
  res->base.create_cons = ddd_create_cons;
  res->base.is_strict = ddd_is_strict;
  res->base.get_term = ddd_get_term;
  res->base.get_constant = ddd_get_constant;
  res->base.negate_cons = ddd_negate_cons;
  res->base.is_negative_cons = ddd_is_negative_cons;
  res->base.is_stronger_cons = ddd_is_stronger_cons;
  res->base.resolve_cons = ddd_resolve_cons;
  res->base.destroy_lincons = ddd_destroy_lincons;
  res->base.dup_lincons = ddd_dup_lincons;
  res->base.to_tdd = ddd_to_tdd;
  res->type = t;
  res->var_num = vn;
  res->cons_node_map = NULL;
  return (theory_t*)res;
}

/**********************************************************************
 * destroy a DDD theory
 *********************************************************************/
void ddd_destroy_theory(theory_t *t)
{
  //free the cons_node_map
  ddd_cons_node_t *cnm = ((ddd_theory_t*)t)->cons_node_map;
  while(cnm) {
    free(cnm);
    cnm = cnm->next;
  }
  //free the theory
  free((ddd_theory_t*)t);
}

/**********************************************************************
 * end of tdd-ddd.c
 *********************************************************************/

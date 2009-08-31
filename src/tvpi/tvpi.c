#include "tvpiInt.h"

tvpi_cst_t 
new_cst ()
{
  mpq_t *r;
  r = (mpq_t*) malloc (sizeof (mpq_t));
  return r;
}

tvpi_cons_t
new_cons ()
{
  
  tvpi_cons_t c;
  
  c = (tvpi_cons_t) malloc (sizeof (struct tvpi_cons));
  return c;

}

tvpi_term_t 
new_term ()
{
  return new_cons ();
}

tvpi_cst_t 
tvpi_create_si_cst (int v)
{
  mpq_t *r = (mpq_t*)malloc (sizeof(mpq_t));
  if (r == NULL) return NULL;
  
  mpq_init (*r);
  mpq_set_si (*r, v, 1);
  return r;
}

tvpi_cst_t 
tvpi_create_si_rat_cst (int num, int den)
{
  mpq_t *r;
  r = new_cst ();
  if (r == NULL) return NULL;

  mpq_init (*r);
  mpq_set_si (*r, num, den);
  mpq_canonicalize (*r);
  return r;
}

tvpi_cst_t 
tvpi_negate_cst (tvpi_cst_t c)
{
  mpq_t *r;
  
  r = (mpq_t*)malloc (sizeof (mpq_t));
  if (r == NULL) return NULL;
  
  mpq_init (*r);
  mpq_set (*r, *c);
  mpq_neg (*r, *r);
  return r;
}

tvpi_cst_t 
tvpi_add_cst (tvpi_cst_t k1, tvpi_cst_t k2)
{
  mpq_t *r;

  r = new_cst ();
  if (r == NULL) return NULL;
  
  mpq_init (*r);
  mpq_add (*r, *k1, *k2);
  return r;
}

tvpi_cst_t
tvpi_mul_cst (tvpi_cst_t k1, tvpi_cst_t k2)
{
  mpq_t *r;

  r = new_cst ();
  if (r == NULL) return NULL;
  
  mpq_init (*r);
  mpq_mul (*r, *k1, *k2);
  return r;
}

/**
 * Returns 1 if k > 0, 0 if k = 0, and -1 if k < 0
 */
int 
tvpi_sgn_cst (tvpi_cst_t k)
{
  return mpq_sgn (*k);
}


bool 
alwasy_false_cst (tvpi_cst_t k)
{
  return 0;
}

int
tvpi_terms_have_resolvent (tvpi_term_t t1, tvpi_term_t t2, int x)
{
  /* XXX: TODO */
  return 0;
}


void 
tvpi_destroy_cst (tvpi_cst_t k)
{
  mpq_clear (*k);
  free (k);
}



tvpi_term_t 
tvpi_create_linterm (int* coeff, size_t n)
{
  /* term to be created */
  tvpi_term_t t;
  /* array iterator */
  size_t i;

  /* current term variable for which coefficient is thought */
  int v;
  
  t = new_term ();

  t->var [0] = -1;
  t->var [1] = -1;
  
  /* scan coeff array to extract coefficients for at most two variables */
  v = 0;
  for (i = 0; i < n; i++)
    {
      if (coeff [i] != 0)
	{
	  t->var [v] = i;
	  if (v == 0) 
	    {
	      t->negative = (coeff [i] < 0);
	      t->fst_coeff = 
		tvpi_create_si_cst (t->negative ? -coeff[i] : coeff[i]);
	    }
	  else 
	    t->coeff = tvpi_create_si_cst (coeff [i]);
	  v++;
	  if (v >= 2) break;
	}
    }
  assert (v >= 1);

  /* if no second variable, set coeff to 0 */
  if (v == 1) 
    { 
      t->coeff = new_cst ();
      mpq_init (*(t->coeff));
    }
  return t;
}

bool
tvpi_term_equlas (tvpi_term_t t1, tvpi_term_t t2)
{
  return t1->negative == t2->negative &&
    t1->var [0] == t2->var [0] &&
    t1->var [1] == t2->var [1] &&
    mpq_cmp (*t1->coeff, *t2->coeff) == 0 &&
    ((t1->fst_coeff == NULL && t2->fst_coeff == NULL) ||
     (mpq_cmp (*t1->fst_coeff, *t2->fst_coeff) == 0));
}


bool 
tvpi_term_has_var (tvpi_term_t t, int var)
{
  return t->var[0] == var || (IS_VAR (t->var [1]) && t->var [1] == var);
}

bool
tvpi_term_has_vars (tvpi_term_t t, int *vars)
{
  return vars [t->var[0]] || (IS_VAR (t->var [1]) && vars [t->var [1]]);
}

void
tvpi_var_occurrences (tvpi_cons_t c, int *o)
{
  o [c->var[0]]++;
  if (IS_VAR(c->var [1])) o [c->var[1]]++;
}


size_t
tvpi_num_of_vars (tvpi_theory_t *self)
{
  return self->var_num;
}

void
tvpi_print_cst (FILE *f, tvpi_cst_t k)
{
  mpq_out_str (f, 10, *k);
}

void
tvpi_print_term (FILE *f, tvpi_term_t t)
{
  if (t->negative)
    fprintf (f, "%s", "-");
  
  if (t->fst_coeff != NULL)
    tvpi_print_cst (f, t->fst_coeff);
  fprintf (f, "x%d", t->var [0]);
  
  if (IS_VAR (t->var [1]))
    {
      if (mpq_sgn (*t->coeff) >= 0)
	fprintf (f, "+");
      tvpi_print_cst (f, t->coeff);
      fprintf (f, "x%d", t->var [1]);
    }
}

void 
tvpi_print_cons (FILE *f, tvpi_cons_t c)
{
  mpq_t k1, k2;
  char *op1, *op2;
  
  mpq_init (k1);
  mpq_set (k1, *(c->coeff));
  mpq_init (k2);
  mpq_set (k2, *(c->cst));

  if (c->negative) 
    { 
      mpq_neg (k1, k1);
      mpq_neg (k2, k2);
      op2 = c->strict ? ">" : ">=";
    }
  else
    op2 = c->strict ? "<" : "<=";

  op1 =  (mpq_sgn (k1) >= 0) ? "+" : "";
  if (IS_VAR (c->var [1]))
    fprintf (f, "x%d%sx%d%s", c->var[0], op1, c->var[1], op2);
  else
    fprintf (f, "x%d%s", c->var[0], op2);
  mpq_out_str (f, 10, k2);

  mpq_clear (k1);
  mpq_clear (k2);
}

tvpi_term_t
tvpi_dup_term (tvpi_term_t t)
{
  tvpi_term_t r;
  
  r = new_term ();
  r->negative = t->negative;
  r->var[0] = t->var[0];
  r->var[1] = t->var[1];
  
  r->coeff = new_cst ();
  mpq_init (*r->coeff);
  mpq_set (*r->coeff, *t->coeff);
  
  if (t->fst_coeff != NULL)
    {
      r->fst_coeff = new_cst ();
      mpq_init (*r->fst_coeff);
      mpq_set (*r->fst_coeff, *t->fst_coeff);
    }

  return r;
}

/**
 * Returns term for -1*t
 */
tvpi_term_t
tvpi_negate_term (tvpi_term_t t)
{
  tvpi_term_t r;
  
  r = tvpi_dup_term (t);
  r->negative = t->negative ? 0 : 1;
  if (IS_VAR (t->var [1])) mpq_neg (*r->coeff, *r->coeff);
  return r;
}

int
tvpi_pick_var (tvpi_term_t t, bool *vars)
{
  if (vars [t->var [0]]) return t->var [0];
  if (IS_VAR (t->var [1]) && vars [t->var [1]]) return t->var [1];
  return -1;
}

void
tvpi_destroy_term (tvpi_term_t t)
{
  mpq_clear (*t->coeff);
  if (t->fst_coeff != NULL)
    mpq_clear (*t->fst_coeff);
  free (t);
}

/**
 * Creates a new constraint t <= k (if s = 0), or t < k (if s != 0)
 * Side-effect: t and k become owned by the constraint.
 */
tvpi_cons_t 
tvpi_create_cons (tvpi_term_t t, bool s, tvpi_cst_t k)
{
  t->cst = k;
  t->strict = s;
  /* divide everything by the coefficient of var[0], if there is one */
  if (t->fst_coeff != NULL)
    {
      mpq_div (*t->cst, *t->cst, *t->fst_coeff);
      mpq_div (*t->coeff, *t->coeff, *t->fst_coeff);
      tvpi_destroy_cst (t->fst_coeff);
      t->fst_coeff = NULL;
    }

  return (tvpi_cons_t)t;
}

bool
tvpi_is_strict (tvpi_cons_t c)
{
  return c->strict;
}

tvpi_term_t 
tvpi_get_term (tvpi_cons_t c)
{
  return c;
}

tvpi_cst_t 
tvpi_dup_cst (tvpi_cst_t k)
{
  tvpi_cst_t r = new_cst ();

  mpq_init (*r);
  mpq_set (*r, *k);
  return r;
}

tvpi_cst_t
tvpi_get_cst (tvpi_cons_t c)
{
  return c->cst;
}

tvpi_cons_t 
tvpi_dup_cons (tvpi_cons_t c)
{
  tvpi_cons_t r;

  r = tvpi_dup_term (c);
  r->strict = c->strict;
  r->cst = new_cst ();
  mpq_init (*r->cst);
  mpq_set (*(r->cst), *(c->cst));

  return r;
}


tvpi_cons_t
tvpi_negate_cons (tvpi_cons_t c)
{
  tvpi_cons_t r;

  /* negate the term constraint */
  r = tvpi_negate_term (c);
  
  r->strict = !r->strict;
  r->cst = tvpi_negate_cst (c->cst);
  return r;
}

bool
tvpi_is_neg_cons (tvpi_cons_t c)
{
  return c->negative;
}

bool
tvpi_is_stronger_cons (tvpi_cons_t c1, tvpi_cons_t c2)
{
  return tvpi_term_equlas (c1, c2) && mpq_cmp (*(c1->cst), *(c2->cst)) <= 0;
}

tvpi_cons_t
tvpi_resolve_cons (tvpi_cons_t c1, tvpi_cons_t c2, int x)
{
  /* index of x in c1 and c2, respectively */
  int idx_xc1;
  int idx_xc2;
  int idx_nxc1;
  int idx_nxc2;

  /* coefficient in the resolvent of the of NOT x variable in c1 */
  mpq_t coeff_nxc1;
  /* coeffcient in the resolvent of the of NOT x variable in c2 */
  mpq_t coeff_nxc2;

  mpq_t coeff_xc1;
  mpq_t coeff_xc2;
  mpq_t tmp;

  tvpi_cons_t c;


  c = new_cons ();
  c->fst_coeff = NULL;
  c->strict = ((!c1->strict) && (!c2->strict));
  c->cst = new_cst ();
  
  assert (c1->var[0] == x || c1->var[1] == x);
  assert (c2->var[0] == x || c2->var[1] == x);
  assert (IS_VAR (c1->var [1]) && IS_VAR (c2->var [1]));

  /* XXX: It is possible that c1->var [1] == c2->var [1]. This case is
     not handled properly right now!
  */

  idx_xc1 = (c1->var [0] == x) ? 0 : 1;
  idx_xc2 = (c2->var [0] == x) ? 0 : 1;
  idx_nxc1 = 1 - idx_xc1;
  idx_nxc2 = 1 - idx_xc2;
  
  mpq_init (coeff_xc1);
  mpq_init (coeff_xc2);
  
  if (idx_c1 == 0)
    mpq_set_si (coeff_xc1, 1, 1);
  else
    {
      mpq_set (coeff_xc1, *c1->coeff);
      mpq_abs (coeff_xc1, coeff_xc1);
  
  if (idx_c2 == 0)
    mpq_set_si (coeff_xc2, 1, 1);
  else
    {
      mpq_set (coeff_xc2, *c2->coeff);
      mpq_abs (coeff_xc2, coeff_xc2);
    }

  
  /* compute constant */
  mpq_init (*c->cst);
  mpq_mul (*c->cst, coeff_xc2, *c1->cst);
  
  mpq_init (tmp);
  mpq_mul (tmp, coeff_xc1, *c2->cst);

  mpq_add (*c->cst, *c->cst, tmp);
  mpq_clear (tmp);
  
  /* compute coefficient of nxc1 */
  mpq_init (coeff_nxc1);
  if (idx_nxc1 == 0)
    {
      mpq_set (coeff_nxc1, coeff_xc2);
      if (c1->negative)
	mpq_neg (coeff_nxc1, coeff_nxc1);
    }
  else
    mpq_mul (coeff_nxc1, coeff_xc2, c1->coeff);

  /* compute coefficient of nxc2 */
  mpq_init (coeff_nxc2);
  if (idx_nxc2 == 0)
    {
      mpq_set (coeff_nxc2, coeff_xc1);
      if (c2->negative)
	mpq_neg (coeff_nxc2, coeff_nxc2);
    }
  else
    mpq_mul (coeff_nxc2, coeff_xc1, c2->coeff);

  c->coeff = new_cst ();
  mpq_init (*c->coeff);
  
  /* at least one of coeff_nxc1 and coeff_nxc2 cannot be 0 */
  if (c1->var[idx_nxc1] < c2->var[idx_nxc2] && 
      mpq_sgn (coeff_nxc1) != 0)
    {
      c->var [0] = c1->var [idx_nxc1];
      c->var [1] = c2->var [dix_nxc2];
      c->negative = (mpq_sgn (coeff_nxc1) < 0);
      if (c->negative)
	mpq_neg (coeff_nxc1, coeff_nxc1);
      
      mpq_div (*c->coeff, coeff_nxc2, coeff_nxc1);
      mpq_div (*c->cst, coeff_nxc1);
    }
  else 
    {
      c->var [0] = c1->var [idx_nxc2];
      c->var [1] = c2->var [dix_nxc1];
      c->negative = (mpq_sgn (coeff_nxc2) < 0);
      if (c->negative)
	mpq_neg (coeff_nxc2, coeff_nxc2);
      
      mpq_div (*c->coeff, coeff_nxc1, coeff_nxc2);
      mpq_div (*c->cst, coeff_nxc2);
    }

  mpq_clear (coeff_xc1);
  mpq_clear (coeff_nxc1);
  mpq_clear (coeff_xc2);
  mpq_clear (coeff_nxc2);

  /* c->coeff can be 0. Make sure that var[1] is unset in that case */
  if (mpq_sgn (*c->coeff) == 0) c->var[1] = -1;

  return c;
}

void
tvpi_destroy_cons (tvpi_cons_t c)
{
  mpq_clear (*(c->cst));
  free (c);
}

/**
 * Returns a DD representing a constraint.
 */
tdd_node*
tvpi_get_dd (tdd_manager *m, tvpi_theory_t* t, tvpi_cons_t c)
{
  return NULL;
}

tdd_node*
tvpi_to_tdd(tdd_manager *m, tvpi_cons_t c)
{
  /* the theory */
  tvpi_theory_t *theory;

  /* the new constraint */
  tvpi_cons_t nc;
  
  tdd_node *res;

  theory = (tvpi_theory_t*) (m->theory);

  nc = c->negative ? tvpi_negate_cons (c) : c;

  res = tvpi_get_dd (m, theory, nc);
  
  if (c->negative)
    tvpi_destroy_cons (nc);
  
  return  (c->negative && res != NULL ? tdd_not (res) : res);
}


theory_t *
tvpi_create_theory (size_t vn)
{
  tvpi_theory_t * t;
  int i;
  
  t = (tvpi_theory_t*) malloc (sizeof (tvpi_theory_t));
  if (t == NULL) return NULL;

  /* initialize the map */
  t->var_num = vn;
  /* t->map = (tvpi_list_node_t**) malloc (sizeof (tvpi_list_node_t*) * t->var_num); */
  if (t->map == NULL)
    {
      free (t);
      return NULL;
    }
  for (i = 0; i < t->var_num; i++)
    t->map [i] = NULL;
  
  
  t->base.create_int_cst =  (constant_t(*)(int)) tvpi_create_si_cst;
  t->base.create_rat_cst = (constant_t(*)(int,int)) tvpi_create_si_rat_cst;
  t->base.dup_cst = (constant_t(*)(constant_t)) tvpi_dup_cst;
  t->base.negate_cst = (constant_t(*)(constant_t)) tvpi_negate_cst;
  t->base.is_pinf_cst = (int(*)(constant_t))alwasy_false_cst;
  t->base.is_ninf_cst = (int(*)(constant_t))alwasy_false_cst;

  t->base.destroy_cst = (void(*)(constant_t))tvpi_destroy_cst;
  t->base.add_cst = (constant_t(*)(constant_t,constant_t))tvpi_add_cst;
  t->base.mul_cst = (constant_t(*)(constant_t,constant_t))tvpi_mul_cst;
  t->base.sgn_cst = (int(*)(constant_t))tvpi_sgn_cst;

  t->base.create_linterm = (linterm_t(*)(int*,size_t))tvpi_create_linterm;
  t->base.dup_term = (linterm_t(*)(linterm_t))tvpi_dup_term;
  t->base.term_equals = (int(*)(linterm_t,linterm_t))tvpi_term_equlas;
  t->base.term_has_var = (int(*)(linterm_t,int)) tvpi_term_has_var;
  t->base.term_has_vars = (int(*)(linterm_t,int*)) tvpi_term_has_vars;
  t->base.var_occurrences = (void(*)(lincons_t,int*))tvpi_var_occurrences;

  t->base.terms_have_resolvent = 
    (int(*)(linterm_t,linterm_t,int))tvpi_terms_have_resolvent;
  t->base.negate_term = (linterm_t(*)(linterm_t))tvpi_negate_term;
  t->base.pick_var = (int(*)(linterm_t,int*))tvpi_pick_var;
  t->base.destroy_term = (void(*)(linterm_t))tvpi_destroy_term;
  
  t->base.create_cons = (lincons_t(*)(linterm_t,int,constant_t))tvpi_create_cons;
  t->base.is_strict = (bool(*)(lincons_t))tvpi_is_strict;
  t->base.get_term = (linterm_t(*)(lincons_t))tvpi_get_term;
  t->base.get_constant = (constant_t(*)(lincons_t))tvpi_get_cst;
  t->base.negate_cons = (lincons_t(*)(lincons_t))tvpi_negate_cons;
  t->base.is_negative_cons = (int(*)(lincons_t))tvpi_is_neg_cons;
  t->base.resolve_cons = 
    (lincons_t(*)(lincons_t,lincons_t,int))tvpi_resolve_cons;
  t->base.dup_lincons = (lincons_t(*)(lincons_t)) tvpi_dup_cons;
  t->base.is_stronger_cons = 
    (int(*)(lincons_t,lincons_t)) tvpi_is_stronger_cons;
  t->base.destroy_lincons = (void(*)(lincons_t)) tvpi_destroy_cons;
  

  t->base.to_tdd = (tdd_node*(*)(tdd_manager*,lincons_t))tvpi_to_tdd;
  t->base.print_lincons = (void(*)(FILE*,lincons_t))tvpi_print_cons;

  t->base.num_of_vars = (size_t(*)(theory_t*))tvpi_num_of_vars;
  
  

  
  /* unimplemented */
  t->base.create_double_cst = NULL;
  t->base.theory_debug_dump = NULL;
  t->base.qelim_init = NULL;
  t->base.qelim_push = NULL;
  t->base.qelim_pop = NULL;
  t->base.qelim_solve = NULL;
  t->base.qelim_destroy_context = NULL;

  return (theory_t*)t;
}

void 
tvpi_destroy_theory (theory_t *theory)
{
  tvpi_theory_t* t;
  /* int i; */
  
  t = (tvpi_theory_t*)theory;

  /* destroy the map */
  /* for (i = 0; i < t->var_num; i++) */
  /*   { */
  /*     tvpi_list_node_t* p; */
  /*     if (t->map [i] == NULL) continue; */
      
  /*     p = t->map [i]; */
  /*     while (p != NULL) */
  /* 	{ */
  /* 	  tvpi_list_node_t* next; */
  /* 	  next = p->next; */
  /* 	  free (p); */
  /* 	  p = next; */
  /* 	} */
  /*     t->map [i] = NULL; */
  /*   } */
  free (t->map);
  t->map = NULL;
  free (t);
}

#include "boxInt.h"



box_cst_t 
new_cst ()
{
  mpz_t *r;
  r = (mpz_t*) malloc (sizeof (mpz_t));
  return r;
}

box_cons_t
new_cons ()
{
  
  box_cons_t c;
  
  c = (box_cons_t) malloc (sizeof (struct box_cons));
  return c;

}

box_term_t 
new_term ()
{
  return new_cons ();
}

box_cst_t 
box_create_si_cst (int v)
{
  mpz_t *r = (mpz_t*)malloc (sizeof(mpz_t));
  if (r == NULL) return NULL;
  
  mpz_init_set_si (*r, v);
  return r;
}


box_cst_t 
box_negate_cst (box_cst_t c)
{
  mpz_t *r;
  
  r = (mpz_t*)malloc (sizeof (mpz_t));
  if (r == NULL) return NULL;
  
  mpz_init_set (*r, *c);
  mpz_neg (*r, *r);
  return r;
}

box_cst_t 
box_add_cst (box_cst_t k1, box_cst_t k2)
{
  mpz_t *r;
  
  mpz_init (*r);
  mpz_add (*r, *k1, *k2);
  return r;
}

box_cst_t
box_mul_cst (box_cst_t k1, box_cst_t k2)
{
  mpz_t *r;
  
  mpz_init (*r);
  mpz_mul (*r, *k1, *k2);
  return r;
}

int
box_is_pos_cst (box_cst_t k)
{
  return mpz_sgn (*k) >= 0;
}

int
box_is_zero_cst (box_cst_t k)
{
  return mpz_sgn (*k) == 0;
}


bool 
alwasy_false_cst (box_cst_t k)
{
  return 0;
}

int
box_terms_have_resolvent (box_term_t t1, box_term_t t2, int x)
{
  return 0;
}


void 
box_destroy_cst (box_cst_t k)
{
  mpz_clear (*k);
  free (k);
}



box_term_t 
box_create_linterm (int* coeff, size_t n)
{
  box_term_t t;
  size_t i;
  
  t = new_term ();

  for (i = 0; i < n; i++)
    {
      if (coeff [i] == 1 || 
	  coeff [i] == -1)
	{
	  t->var = i;
	  t->negative = (coeff [i] == -1);
	  break;
	}
      assert (coeff [i] == 0 && "Legal coefficients are {-1,0,1}");
    }
  
  return t;
}

bool
box_term_equlas (box_term_t t1, box_term_t t2)
{
  return t1->var == t2->var && t1->negative == t2->negative;
}


bool 
box_term_has_var (box_term_t t, int var)
{
  return t->var == var;
}

bool
box_term_has_vars (box_term_t t, int *vars)
{
  return vars [t->var];
}

void
box_var_occurrences (box_cons_t c, int *o)
{
  o [c->var]++;
}


size_t
box_num_of_vars (box_theory_t *self)
{
  return self->var_num;
}

void
box_print_cst (FILE *f, box_cst_t k)
{
  mpz_out_str (f, 10, *k);
}

void
box_print_term (FILE *f, box_term_t t)
{
  fprintf (f, "%sx%d", (t->negative ? "-" : ""), t->var);
}

void 
box_print_cons (FILE *f, box_cons_t c)
{
  mpz_t k;
  char* op;
  
  mpz_init_set (k, *(c->cst));

  if (c->negative) 
    { 
      mpz_neg (k, k);
      op = (c->strict ? ">" : ">=");
    }
  else
    op = (c->strict ? "<" : "<=");

  fprintf (f, "x%d%s", c->var, op);
  mpz_out_str (f, 10, k);
}

box_term_t
box_dup_term (box_term_t t)
{
  box_term_t r;
  
  r = new_term ();
  r->negative = t->negative;
  r->var = t->var;

  return r;
}

box_term_t
box_negate_term (box_term_t t)
{
  box_term_t r;
  
  r = box_dup_term (t);
  r->negative = !r->negative;
  return r;
}

int
box_pick_var (box_term_t t, bool *vars)
{
  return vars[t->var] ? t->var : -1;
}

void
box_destroy_term (box_term_t t)
{
  free (t);
}

/**
 * Creates a new constraint t <= k (if s = 0), or t < k (if s != 0)
 * Side-effect: t and k become owned by the constraint.
 */
box_cons_t 
box_create_cons (box_term_t t, bool s, box_cst_t k)
{
  t->cst = k;

  /* Integers:  x < k IFF  x <= k */
  if (s)
    mpz_sub_ui (*(t->cst), *(t->cst), 1);
  
  t->strict = 0;
  
  return (box_cons_t)t;
}

bool
box_is_strict (box_cons_t c)
{
  return c->strict;
}

box_term_t 
box_get_term (box_cons_t c)
{
  return c;
}

box_cst_t 
box_dup_cst (box_cst_t k)
{
  box_cst_t r = new_cst ();
  
  mpz_init_set (*r, *k);
  return r;
}

box_cst_t
box_get_cst (box_cons_t c)
{
  return c->cst;
}

box_cons_t 
box_dup_cons (box_cons_t c)
{
  box_cons_t r;
  
  r = new_cons ();
  r->strict = c->strict;
  r->negative = c->negative;
  r->var = c->var;
  r->cst = new_cst ();
  mpz_init_set (*(r->cst), *(c->cst));

  return r;
}


box_cons_t
box_negate_cons (box_cons_t c)
{
  box_cons_t r;
  
  r = box_dup_cons (c);
  mpz_neg (*(r->cst), *(r->cst));
  r->strict = !r->strict;
  r->negative = !r->negative;

  /* normalize constraint if it became strict inequality */
  if (r->strict)
    {
      r->strict = 0;
      mpz_sub_ui (*(r->cst), *(r->cst), 1);
    }
  return r;
}

bool
box_is_neg_cons (box_cons_t c)
{
  return c->negative;
}

bool
box_is_stronger_cons (box_cons_t c1, box_cons_t c2)
{
  return c1->negative == c2->negative && c1->var == c2->var && 
    mpz_cmp (*(c1->cst), *(c2->cst)) <= 0;
}

box_cons_t
box_resolve_cons (box_cons_t c1, box_cons_t c2, int x)
{
  return NULL;
}

void
box_destroy_cons (box_cons_t c)
{
  mpz_clear (*(c->cst));
  free (c);
}

/**
 * Returns a DD representing a constraint.
 */
tdd_node*
box_get_dd (tdd_manager *m, box_theory_t* t, box_cons_t c)
{
  box_list_node_t * ln;
  box_list_node_t *p;
  int i;

  /* get the head of the list node for the variable of the constraint */
  ln = t->map [c->var];
  
  /* first constraint */
  if (ln == NULL)
    {
      ln = (box_list_node_t*) malloc (sizeof (box_list_node_t));
      if (ln == NULL) return NULL;
      ln->prev = NULL;
      ln->next = NULL;
      ln->cons = box_dup_cons (c);
      ln->dd = tdd_new_var (m, (lincons_t)ln->cons);
      tdd_ref (ln->dd);

      /* wire ln into the map */
      t->map [c->var] = ln;
      return ln->dd;
    }

  assert (ln != NULL);
  /* find a place to insert c */
  p = ln;
  while (1)
    {
      i = mpz_cmp (*(p->cons->cst), *(c->cst));
      if (i >= 0) break;
      
      if (p->next == NULL) break;
      p = p->next;
    }
  
  /* at this point, p != NULL and i is the comparison value between p->cons and c */
  assert (p != NULL);
    
  /* p->cons is same as c */
  if (i == 0)
    return p->dd;
  /* c  precedes p->cons, insert before p->cons in the list */
  else if (i > 0)
    {
      box_list_node_t *n;
	      
      n = (box_list_node_t*)malloc (sizeof (box_list_node_t));
      if (n == NULL) return NULL;
      n->next = p;
      n->prev = p->prev;
      p->prev = n;
	      
      n->cons = box_dup_cons (c);
      n->dd = tdd_new_var_before (m, p->dd, (lincons_t)n->cons);
      tdd_ref (n->dd);

      /* update the head of the list if needed */
      if (t->map [c->var] == p)
	t->map [c->var] = n;

      return n->dd;      
    }
  /* p->cons precedes c */
  else if (i < 0)
    {
      box_list_node_t *n;
	  
      n = (box_list_node_t*)malloc (sizeof (box_list_node_t));
      if (n == NULL) return NULL;
      n->prev = p;
      n->next = p->next;
      p->next = n;

      n->cons = box_dup_cons (c);
      n->dd = tdd_new_var_after (m, p->dd, (lincons_t)n->cons);
      tdd_ref (n->dd);
      return n->dd;
    }
  
  assert (0 && "UNREACHABLE");
}


tdd_node*
box_to_tdd(tdd_manager *m, box_cons_t c)
{
  /* the theory */
  box_theory_t *theory;

  /* the new constraint */
  box_cons_t nc;
  
  tdd_node *res;

  theory = (box_theory_t*) (m->theory);

  nc = c->negative ? box_negate_cons (c) : c;

  res = box_get_dd (m, theory, nc);
  
  if (c->negative)
    box_destroy_cons (nc);
  
  return  (c->negative && res != NULL ? tdd_not (res) : res);
}


theory_t *
box_create_theory (size_t vn)
{
  box_theory_t * t;
  int i;
  
  t = (box_theory_t*) malloc (sizeof (box_theory_t));
  if (t == NULL) return NULL;

  /* initialize the map */
  t->var_num = vn;
  t->map = (box_list_node_t**) malloc (sizeof (box_list_node_t*) * t->var_num);
  if (t->map == NULL)
    {
      free (t);
      return NULL;
    }
  for (i = 0; i < t->var_num; i++)
    t->map [i] = NULL;
  
  
  t->base.create_int_cst =  (constant_t(*)(int)) box_create_si_cst;
  t->base.dup_cst = (constant_t(*)(constant_t)) box_dup_cst;
  t->base.negate_cst = (constant_t(*)(constant_t)) box_negate_cst;
  t->base.is_pinf_cst = (int(*)(constant_t))alwasy_false_cst;
  t->base.is_ninf_cst = (int(*)(constant_t))alwasy_false_cst;

  t->base.destroy_cst = (void(*)(constant_t))box_destroy_cst;
  t->base.add_cst = (constant_t(*)(constant_t,constant_t))box_add_cst;
  t->base.mul_cst = (constant_t(*)(constant_t,constant_t))box_mul_cst;
  t->base.is_zero_cst = (int(*)(constant_t))box_is_zero_cst;
  t->base.is_pos_cst = (int(*)(constant_t))box_is_pos_cst;

  t->base.create_linterm = (linterm_t(*)(int*,size_t))box_create_linterm;
  t->base.dup_term = (linterm_t(*)(linterm_t))box_dup_term;
  t->base.term_equals = (int(*)(linterm_t,linterm_t))box_term_equlas;
  t->base.term_has_var = (int(*)(linterm_t,int)) box_term_has_var;
  t->base.term_has_vars = (int(*)(linterm_t,int*)) box_term_has_vars;
  t->base.var_occurrences = (void(*)(lincons_t,int*))box_var_occurrences;

  t->base.terms_have_resolvent = 
    (int(*)(linterm_t,linterm_t,int))box_terms_have_resolvent;
  t->base.negate_term = (linterm_t(*)(linterm_t))box_negate_term;
  t->base.pick_var = (int(*)(linterm_t,int*))box_pick_var;
  t->base.destroy_term = (void(*)(linterm_t))box_destroy_term;
  
  t->base.create_cons = (lincons_t(*)(linterm_t,int,constant_t))box_create_cons;
  t->base.is_strict = (bool(*)(lincons_t))box_is_strict;
  t->base.get_term = (linterm_t(*)(lincons_t))box_get_term;
  t->base.get_constant = (constant_t(*)(lincons_t))box_get_cst;
  t->base.negate_cons = (lincons_t(*)(lincons_t))box_negate_cons;
  t->base.is_negative_cons = (int(*)(lincons_t))box_is_neg_cons;
  t->base.resolve_cons = 
    (lincons_t(*)(lincons_t,lincons_t,int))box_resolve_cons;
  t->base.dup_lincons = (lincons_t(*)(lincons_t)) box_dup_cons;
  t->base.is_stronger_cons = 
    (int(*)(lincons_t,lincons_t)) box_is_stronger_cons;
  t->base.destroy_lincons = (void(*)(lincons_t)) box_destroy_cons;
  

  t->base.to_tdd = (tdd_node*(*)(tdd_manager*,lincons_t))box_to_tdd;
  t->base.print_lincons = (void(*)(FILE*,lincons_t))box_print_cons;

  t->base.num_of_vars = (size_t(*)(theory_t*))box_num_of_vars;
  
  

  
  /* unimplemented */
  t->base.create_rat_cst = NULL;
  t->base.create_double_cst = NULL;
  t->base.theory_debug_dump = NULL;
  t->base.qelim_init = NULL;
  t->base.qelim_push = NULL;
  t->base.qelim_pop = NULL;
  t->base.qelim_solve = NULL;
  t->base.qelim_destroy_context = NULL;

  /* need to implement */
  

  return (theory_t*)t;
}

void 
box_destroy_theory (theory_t *theory)
{
  box_theory_t* t;
  int i;
  
  t = (box_theory_t*)theory;

  /* destroy the map */
  for (i = 0; i < t->var_num; i++)
    {
      box_list_node_t* p;
      if (t->map [i] == NULL) continue;
      
      p = t->map [i];
      while (p != NULL)
	{
	  box_list_node_t* next;
	  next = p->next;
	  free (p);
	  p = next;
	}
      t->map [i] = NULL;
    }
  free (t->map);
  t->map = NULL;
  free (t);
}

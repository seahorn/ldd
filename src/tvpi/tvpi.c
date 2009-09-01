#include "tvpiInt.h"

static tvpi_cst_t 
new_cst ()
{
  mpq_t *r;
  r = (mpq_t*) malloc (sizeof (mpq_t));
  return r;
}

static tvpi_cons_t
new_cons ()
{
  
  tvpi_cons_t c;
  
  c = (tvpi_cons_t) malloc (sizeof (struct tvpi_cons));
  c->fst_coeff = NULL;
  return c;

}

static tvpi_term_t 
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
tvpi_create_d_cst (double d)
{
  mpq_t *r;
  r = new_cst ();
  if (r == NULL) return NULL;
  
  mpq_init (*r);
  mpq_set_d (*r, d);

  return r;
}

tvpi_cst_t 
tvpi_negate_cst (tvpi_cst_t c)
{
  mpq_t *r;
  
  r = new_cst ();
  if (r == NULL) return NULL;
  
  mpq_init (*r);
  mpq_neg (*r, *c);
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


static bool 
always_false_cst (tvpi_cst_t k)
{
  return 0;
}

/**
 * Checks whether t1 and t2 have a resolvent on x.
 * Returns >1 if t1 resolves with t2
 * Returns <1 if t1 resolves with -t2
 * Return 0 if there is no resolvent.
 * Requires: t1 and t2 are normalized terms.
 */
int
tvpi_terms_have_resolvent (tvpi_term_t t1, tvpi_term_t t2, int x)
{

  int sgn_x_in_t1;
  int sgn_x_in_t2;
  
  assert (!t1->negative && !t2->negative && 
	  t1->fst_coeff == NULL && t2->fst_coeff == NULL);


  /* a term with a single variable has not resolvents with anything */
  if (!IS_VAR (t1->var [1]) || !IS_VAR (t2->var [1])) return 0;
  

  sgn_x_in_t1 = 0;
  sgn_x_in_t2 = 0;

  /* compute sign of x in t1 */
  if (t1->var[0] == x) sgn_x_in_t1 = t1->negative ? -1 : 1;
  else if (t1->var [1] == x) sgn_x_in_t1 = mpq_sgn (*t1->coeff);
  
  /* no x in t1, can't resolve */
  if (sgn_x_in_t1 == 0) return 0;
  
  /* compute sign of x in t2 */
  if (t2->var[0] == x) sgn_x_in_t2 = t2->negative ? -1 : 1;
  else if (t2->var [1] == x) sgn_x_in_t2 = mpq_sgn (*t1->coeff);
  
  /* no x in t2, can't resolve */
  if (sgn_x_in_t2 == 0) return 0;

  /* sign of x differs in t1 and t2, so can resolve */
  if (sgn_x_in_t1 != sgn_x_in_t2) return 1;

  /* x has the same sign in both t1 and t2. Can resolve t1 and -t2, but only if 
   * t1 != t2 
   */

  /* check whether t1 == t2 */
  if (t1->var [0] == t2->var[0] && 
      t1->var [1] == t2->var[1] &&
      mpq_cmp (*t1->coeff, *t2->coeff) == 0) return 0;

  return -1;
}


void 
tvpi_destroy_cst (tvpi_cst_t k)
{
  mpq_clear (*k);
  free (k);
}



tvpi_term_t 
tvpi_create_term (int* coeff, size_t n)
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
	      /* absolute value of the coefficient */
	      int abs;
	      t->negative = (coeff [i] < 0);
	      abs = t->negative ? -coeff [i] : coeff [i];
	      /* if |coeff| == 1, then ignore it since will not need to divide
	       * by it to normalize a constraint 
	       */
	      t->fst_coeff = (abs == 1 ? NULL : tvpi_create_si_cst (abs));
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
      
      if (mpq_cmp_si (*t->coeff, 1, 1) == 0)
	;
      else if (mpq_cmp_si (*t->coeff, -1, 1) == 0)
	fprintf (f, "-");
      else
	{   
	  tvpi_print_cst (f, t->coeff);
	  fprintf (f, "*");
	}
      
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
    {
      fprintf (f, "x%d%s", c->var[0], op1);

      /* print the coefficient: print nothing for 1
       * print '-' from -1
       * print 'k*' for any other constant k
       */
      if (mpq_cmp_si (k1, 1, 1) == 0)
	;
      else if (mpq_cmp_si (k1, -1, 1) == 0)
	fprintf (f, "-");
      else
	{
	  mpq_out_str (f, 10, k1);
	  fprintf (f, "*");
	}

      fprintf (f, "x%d%s", c->var[1], op2);
    }  
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
      if (IS_VAR (t->var [1]))
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
  
  r->strict = c->strict ? 0 : 1;
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
  if (tvpi_term_equlas (c1, c2)) 
    {
      /* t <= k IMPLIES t <= m  iff k <= m 
       * t <= k DOES NOT IMPLY t < k
       */
      int i;
      i = mpq_cmp (*c1->cst, *c2->cst);
      if (i < 0) return 1;
      else if (i == 0) return c1->strict || !c2->strict;
    }

  return 0;
}

  


/** 
 * Requires: c1 and c2 are either normalized constraints or negation
 * of a normalized constraint. c1 and c2 have a resolvent on x.
 */
tvpi_cons_t
tvpi_resolve_cons (tvpi_cons_t c1, tvpi_cons_t c2, int x)
{
  /* index of x in c1 */
  int idx_x_c1;
  /* index of x in c2 */
  int idx_x_c2;
  /* index of the other variable in c1 */
  int idx_o_c1;
  /* index of the other variant in c2 */
  int idx_o_c2;
  
  /* the constraint for the result */
  tvpi_cons_t c;

  /* set to >0 if the magnitude of the coefficient of x is the same in c1 and c2 */
  int same_coeff;
  

  assert (c1->var[0] == x || c1->var[1] == x);
  assert (c2->var[0] == x || c2->var[1] == x);
  assert (IS_VAR (c1->var [1]) && IS_VAR (c2->var [1]));

  idx_o_c1 = c1->var [0] == x ? 1 : 0;
  idx_o_c2 = c2->var [0] == x ? 1 : 0;

  /* ensure that the other variable in c1 precedes the other variable
   * in c2 in the variable order */
  if (c1->var [idx_o_c1] > c2->var [idx_o_c2])
    {
      tvpi_cons_t swp;
      swp = c1;
      c1 = c2;
      c2 = swp;
    }

  /* compute idx of x in c1 and c2 */
  idx_x_c1 = 1 - idx_o_c1;
  idx_x_c2 = 1 - idx_o_c2;

  /* compute same_coeff flag */
  if (idx_x_c1 == 0)
    {
      if (idx_x_c2 == 0) same_coeff = 1;
      else
	/* note that we compare  c2->coeff with -coeff of x in c1 */
	same_coeff = (mpq_cmp_si (*c2->coeff, c1->negative ? 1 : -1, 1) == 0);
    }
  else 
    {
      if (idx_x_c2 == 0)
	/* note that we compare c1->coeff with -coeff of x in c2 */
	same_coeff = (mpq_cmp_si (*c1->coeff, c2->negative ? 1 : -1, 1) == 0);
      else
	{
	  mpq_t v1,v2;
	  mpq_init (v1);
	  mpq_init (v2);
	  
	  mpq_abs (v1, *c1->coeff);
	  mpq_abs (v2, *c2->coeff);
	  same_coeff = (mpq_cmp (v1, v2) == 0);
	  mpq_clear (v1);
	  mpq_clear (v2);
	}
    }
  
  
  
  /** allocate the new constraint and it's constants */
  c = new_cons ();
  c->fst_coeff = new_cst ();
  mpq_init (*c->fst_coeff);
  c->coeff = new_cst ();
  mpq_init (*c->coeff);
  c->cst = new_cst ();
  mpq_init (*c->cst);

  /* the resolvent is strict if either one of the arguments is strict */
  c->strict = (c1->strict || c2->strict);
  
  /* variables of the new constraint */
  c->var[0] = c1->var[idx_o_c1];
  c->var[1] = c2->var[idx_o_c2];
  
  /* coefficient of c->var[0] is coeff(c1->var[idx_o_c1]) if
   * coefficients of x have same absolute value in c1 and c2, or
   * coeff (c1->var[idx_o_c1]) * coeff (c2->var[idx_x_c2])
   */
  
  if (idx_o_c1 == 0)
    mpq_set_d (*c->fst_coeff, c1->negative ? -1.0 : 1.0);
  else
    mpq_set (*c->fst_coeff, *c1->coeff);
  
  mpq_set (*c->cst, *c1->cst);
  
  if (!same_coeff && idx_x_c2 != 0)
    {
      /* multiply everything by coeff (c2->var[idx_x_c2]) */
      mpq_t v;
      mpq_init (v);
      mpq_abs (v, *c2->coeff);
      mpq_mul (*c1->fst_coeff, *c1->fst_coeff, v);
      mpq_mul (*c1->cst, *c1->cst, v);
      mpq_clear (v);
    }
  
  /* do the same thing for c->var[1] */
  if (idx_o_c2 == 0)
    mpq_set_d (*c->coeff, c2->negative ? -1.0 : 1.0);
  else
    mpq_set (*c->coeff, *c2->coeff);
  
  if (!same_coeff && idx_x_c1 != 0)
    {
      mpq_t v, u;
      mpq_init (v);
      mpq_init (u);

      mpq_abs (v, *c1->coeff);
      mpq_mul (*c1->coeff, *c1->coeff, v);

      mpq_mul (u, v, *c2->cst);
      mpq_add (*c->cst, *c->cst, u);
      mpq_clear (u);
      mpq_clear (v);
    }
  else
    mpq_add (*c->cst, *c->cst, *c2->cst);

  /* normalize the constraint */

  /* if both variables are the same, add up the coefficients and
     remove second occurrence of the variable */
  if (c->var [0] == c->var[1]) 
    { 
      mpq_add (*c->fst_coeff, *c->fst_coeff, *c->coeff);
      c->var [1] = -1; 
      mpq_set_d (*c->coeff, 0.0); 
    }
  
  /* set the negative flag and absolute value of the first coefficient */
  c->negative = (mpq_sgn (*c->fst_coeff) < 0);
  if (c->negative)
    mpq_abs (*c->fst_coeff, *c->fst_coeff);

  if (mpq_cmp_si (*c->fst_coeff, 1, 1) != 0)
    {
      /* divide everything by first coefficient */
      if (IS_VAR (c->var [1]))
	mpq_div (*c->coeff, *c->coeff, *c->fst_coeff);
      mpq_div (*c->cst, *c->cst, *c->fst_coeff);
    }
  
  /* get rid of first coefficient, it is no longer needed */
  tvpi_destroy_cst (c->fst_coeff);
  c->fst_coeff = NULL;

  return c;  
}

void
tvpi_destroy_cons (tvpi_cons_t c)
{
  mpq_clear (*(c->cst));
  free (c);
}

/**
 * Creates constraint in UTVPI(Z) theory. 
 */
tvpi_cons_t
tvpi_uz_create_cons (tvpi_term_t t, bool s, tvpi_cst_t k)
{
  tvpi_cons_t c;
  /* check that the coefficient in t and constant k are integers */
  assert (!IS_VAR (t->var[1]) || mpz_cmp_si (mpq_denref (*t->coeff), 1) == 0);
  assert (mpz_cmp_si (mpq_denref (*k), 1) == 0);
  
  c = tvpi_create_cons (t, s, k);
  if (c == NULL) return NULL;
  
  if (c->strict)
    {
      mpq_t one;
      mpq_init (one);
      mpq_set_ui (one, 1, 1);
      c->strict = 0;
      mpq_sub (*c->cst, *c->cst, one);
      mpq_clear (one);
    }

  return c;  
}

/**
 * Negates a constraint in UTVPI(Z) theory. 
 */
tvpi_cons_t
tvpi_uz_negate_cons (tvpi_cons_t c)
{
  tvpi_cons_t r;
  
  r = tvpi_negate_cons (c);
  if (r == NULL) return NULL;
  
  if (r->strict)
    {
      mpq_t one;
      mpq_init (one);
      mpq_set_ui (one, 1, 1);
      r->strict = 0;
      mpq_sub (*r->cst, *r->cst, one);
      mpq_clear (one);
    }

  return r;
}





/**
 * Returns a DD representing a constraint.
 */
tdd_node*
tvpi_get_dd (tdd_manager *m, tvpi_theory_t* t, tvpi_cons_t c)
{
  tvpi_list_node_t *ln;
  tvpi_list_node_t *p;
  
  /* keys into the map */
  int var0, var1;
  int i,j;
  
  var0 = c->var[0];
  /* if there is no second variable, use var0 */
  var1 = IS_VAR (c->var [1]) ? c->var[1] : var0;
  
  /* get the head of a link list that holds all constraints with the
     variables of c */
  ln = t->map[var0][var1];

  /* first constraint ever */
  if (ln == NULL)
    {
      ln = (tvpi_list_node_t*) malloc (sizeof (tvpi_list_node_t));
      if (ln == NULL) return NULL;
      
      ln->prev = ln->next = NULL;
      ln->cons = tvpi_dup_cons (c);
      ln->dd = tdd_new_var (m, (lincons_t)(ln->cons));
      assert (ln->dd != NULL);
      tdd_ref (ln->dd);
      
      /* wire into the map */
      t->map [var0][var1] = ln;
      return ln->dd;
    }
  
  assert (ln != NULL);
  
  /* find a place to insert c */
  p = ln;
  
  while (1)
    {
      i = mpq_cmp (*(p->cons->coeff), *(c->coeff));
      
      if (i > 0) break;

      /* same coefficient, check the constant */
      if (i == 0)
	{
	  j = mpq_cmp (*(p->cons->cst), *(c->cst));
	  if (j >= 0) break;
	}
      /* reached end of list */
      if (p->next == NULL) break;
      /* advance */
      p = p->next;
    }

  /* i is the result of comparing the coefficients of p->cons and c
   * if i == 0, then j is the result of comparing the constants of p->cons and c 
   */
  
  /* p->cons equals c */
  if (i == 0 && j == 0)
    {
      return p->dd;
    }
  /* c precedes p->cons, insert before p->cons */
  else if (i > 0 || (i == 0 && j > 0))
    {
      tvpi_list_node_t *n;
      
      n = (tvpi_list_node_t*) malloc (sizeof (tvpi_list_node_t));
      if (n == NULL) return NULL;
      
      n->next = p;
      n->prev = p->prev;
      p->prev = n;
      
      /* add n to the lsit */
      if (n->prev != NULL) /* mid list */
	n->prev->next = n;
      else /* head of the list */
	t->map [var0][var1] = n;
      
      n->cons = tvpi_dup_cons (c);

      /* if this is the first constraint with this term, get a new variable.
       * otherwise, get a new variable that follows p->dd in dd order.
       */
      if (i == 0)
	n->dd = tdd_new_var_before (m, p->dd, (lincons_t)n->cons);
      else
	n->dd = tdd_new_var (m, (lincons_t) n->cons);

      assert (n->dd != NULL);
      tdd_ref (n->dd);

      return n->dd;	  
    }
  /* p->cons precedes c */
  else if (i < 0 || (i == 0 && j < 0))
    {
      tvpi_list_node_t *n;
      
      n = (tvpi_list_node_t*) malloc (sizeof (tvpi_list_node_t));
      if (n == NULL) return NULL;
      
      n->prev = p;
      n->next = p->next;
      p->next = n;
      
      n->cons = tvpi_dup_cons (c);

      /* if this is the first constraint with this term, get a new variable.
       * otherwise, get a new variable that follows p->dd in dd order.
       */
      if (i == 0)
	n->dd = tdd_new_var_after (m, p->dd, (lincons_t)n->cons);
      else
	n->dd = tdd_new_var (m, (lincons_t) n->cons);
      
      assert (n->dd != NULL);
      tdd_ref (n->dd);
      return n->dd;
    }
  

  assert (0 && "UNREACHABLE");
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
  int i, j;
  
  t = (tvpi_theory_t*) malloc (sizeof (tvpi_theory_t));
  if (t == NULL) return NULL;

  t->var_num = vn;

  /* allocate and initialize the map */  
  t->map = (tvpi_list_node_t***) malloc (sizeof (tvpi_list_node_t**) * t->var_num);
  if (t->map == NULL)
    {
      free (t);
      return NULL;
    }

  for (i = 0; i < t->var_num; i++)
    {
      t->map [i] = 
	(tvpi_list_node_t**) malloc (t->var_num * sizeof (tvpi_list_node_t*));
      /* XXX: handle malloc == NULL */
      for (j = 0; j < t->var_num; j++)
	t->map [i][j] = NULL;
    }
  
  
  
  t->base.create_int_cst =  (constant_t(*)(int)) tvpi_create_si_cst;
  t->base.create_rat_cst = (constant_t(*)(int,int)) tvpi_create_si_rat_cst;
  t->base.create_double_cst = (constant_t(*)(double)) tvpi_create_d_cst;
  t->base.dup_cst = (constant_t(*)(constant_t)) tvpi_dup_cst;
  t->base.negate_cst = (constant_t(*)(constant_t)) tvpi_negate_cst;
  t->base.is_pinf_cst = (int(*)(constant_t))always_false_cst;
  t->base.is_ninf_cst = (int(*)(constant_t))always_false_cst;

  t->base.destroy_cst = (void(*)(constant_t))tvpi_destroy_cst;
  t->base.add_cst = (constant_t(*)(constant_t,constant_t))tvpi_add_cst;
  t->base.mul_cst = (constant_t(*)(constant_t,constant_t))tvpi_mul_cst;
  t->base.sgn_cst = (int(*)(constant_t))tvpi_sgn_cst;

  t->base.create_linterm = (linterm_t(*)(int*,size_t))tvpi_create_term;
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
  int i, j;
  
  t = (tvpi_theory_t*)theory;

  for (i = 0; i < t->var_num; i++)
    {
      for (j = 0; j < t->var_num; j++)
	{
	  tvpi_list_node_t *p;
	  
	  p = t->map [i][j];

	  while (p != NULL)
	    {
	      tvpi_list_node_t *next;
	      
	      next = p->next;
	      tvpi_destroy_cons (p->cons);
	      free (p);
	      p = next;
	    }
	  t->map[i][j] = NULL;
	}
      free (t->map [i]);
      t->map [i] = NULL;
    }  
  free (t->map);
  t->map = NULL;
  free (t);
}


/**
 * Creates a theory UTVPI(Z). The constraints are of the form 
 * +-x +-y <= k, where k is in Z
 */
theory_t*
tvpi_create_utvpiz_theory (size_t vn)
{
  tvpi_theory_t* t;
  
  t = (tvpi_theory_t*)tvpi_create_theory (vn);
  if (t == NULL) return NULL;
  

  /* update UTVPI(Z) specific functions.
   * The unique feature of UTVPI(Z) is that t < k is equivalent to t <= (k-1).
   * These following functions ensure that no strict inequalities are created.
   */
  t->base.create_cons = (lincons_t(*)(linterm_t,int,constant_t))tvpi_uz_create_cons;
  t->base.negate_cons = (lincons_t(*)(lincons_t))tvpi_uz_negate_cons;  

  return (theory_t*)t;
}

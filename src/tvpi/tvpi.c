#include "tvpiInt.h"

#ifdef OCT_DEBUG 
#include "tdd-octInt.h" /* enable for debugging */
#endif

static mpq_t *one = NULL;
static mpq_t *none = NULL;

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
  c->op = LEQ;
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
tvpi_create_si_rat_cst (long num, long den)
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
  
  assert (t1->sgn > 0 && t2->sgn > 0 &&
	  t1->fst_coeff == NULL && t2->fst_coeff == NULL);


  /* if both terms have only one variable, cannot resolve on it */
  if (!IS_VAR (t1->var [1]) && !IS_VAR (t2->var [1])) return 0;
  

  sgn_x_in_t1 = 0;
  sgn_x_in_t2 = 0;

  /* compute sign of x in t1 */
  if (t1->var[0] == x) sgn_x_in_t1 = t1->sgn;
  else if (IS_VAR(t1->var[1]) && t1->var [1] == x) 
    sgn_x_in_t1 = mpq_sgn (*t1->coeff);
  
  /* no x in t1, can't resolve */
  if (sgn_x_in_t1 == 0) return 0;
  
  /* compute sign of x in t2 */
  if (t2->var[0] == x) sgn_x_in_t2 = t2->sgn;
  else if (IS_VAR(t2->var[1]) && t2->var [1] == x) 
    sgn_x_in_t2 = mpq_sgn (*t2->coeff);
  
  /* no x in t2, can't resolve */
  if (sgn_x_in_t2 == 0) return 0;

  /* sign of x differs in t1 and t2, so can resolve */
  if (sgn_x_in_t1 * sgn_x_in_t2 < 0) return 1;

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

/**
 * Creates a sparse term. More efficient than tvpi_create_term when
 * the number of variables with non-zero coefficients is small.
 * New term is coeff[0]*var[0] + ... + coeff[n-1] * var[n-1]
 *
 * var   --   array of size n of variables.
 * coeff --   array of size n of coefficients
 *
 * Requires: var is sorted; length of var = length of coeff = n; 1 <= n <= 2;1
 */
tvpi_term_t 
tvpi_create_term_sparse_si (int* var, int* coeff, size_t n)
{
  tvpi_term_t t;
  /* absolute value of the coefficient of var [0] */
  int abs;
  
  assert (n >=1 && n <= 2 && "TVPI allows only 1 or 2 variables per inequality");
  assert ((n == 1 || (var [0] < var [1])) && "Variables must be ordered");
  assert (coeff [0] != 0 && "First coefficient must be non-zero");

  t = new_term ();
  if (t == NULL) return NULL;

  t->var [0] = var[0];
  t->var [1] = n == 2 ? var [1] : -1;
  
  t->sgn = coeff [0] < 0 ? -1 : 1;
  abs = t->sgn > 0 ? coeff [0] : -coeff[0];
  
  if (coeff[0] == 1)
    t->fst_coeff = NULL;
  else
    t->fst_coeff = tvpi_create_si_cst (abs);
  

  if (IS_VAR (t->var [1]))
    t->coeff = tvpi_create_si_cst (coeff [1]);
  else
    {
      t->coeff = new_cst ();
      mpq_init (*t->coeff);
    }

  return t;
}

/** same as tvpi_create_term_sparse, but takes array of constants as
    coefficients instead of array of ints*/
tvpi_term_t tvpi_create_term_sparse (int* var, tvpi_cst_t* coeff, size_t n) 
{ 

  tvpi_term_t t;
  assert (n >=1 && n <= 2 && 
	  "More than 2 variables in inequality");
  assert ((n == 1 || (var [0] < var [1])) && "Variables must be ordered");
  assert (coeff [0] != NULL && "First coefficient cannot be NULL");
  assert (mpz_cmpabs_ui (mpq_numref (*coeff[0]), 0) != 0 && 
	  "First coefficient must be non-zero");

  t = new_term ();
  if (t == NULL) return NULL;

  t->var [0] = var[0];
  t->var [1] = n == 2 ? var [1] : -1;
  
  t->sgn = coeff [0] < 0 ? -1 : 1;
  t->sgn = mpq_sgn (*coeff [0]);

  mpq_abs (*coeff [0], *coeff [0]);
  if (mpq_cmp_ui (*coeff [0], 1, 1) == 0)
    {
      t->fst_coeff = NULL;
      tvpi_destroy_cst (coeff [0]);
    }
  else
    t->fst_coeff = coeff [0];

  if (IS_VAR (t->var [1]))
    t->coeff = coeff [1];
  else
    {
      t->coeff = new_cst ();
      mpq_init (*t->coeff);
    }

  return t;
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
	      t->sgn = (coeff [i] < 0) ? -1 : 1;
	      abs = (coeff [i] < 0) ? -coeff [i] : coeff [i];
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


int 
tvpi_term_size (tvpi_term_t t)
{
  return IS_VAR (t->var [1]) ? 2 : 1;
}

int 
tvpi_term_get_var (tvpi_term_t t, int i)
{
  assert (0 <= i && i <= 1);
  return t->var [i];
}


tvpi_cst_t 
tvpi_term_get_coeff (tvpi_term_t t, int i)
{
  
  assert (0 <= i && i <= 1);

  /* second coefficient is kept explicitly */
  if (i == 1) return t->coeff;
  
  /* see if this is a term with explicit first coefficient */
  if (t->fst_coeff != NULL) return t->fst_coeff;
  
  /* absolute value of the first coefficient is 1, the sign is in t->sgn */
  return t->sgn > 0 ? one : none;
}




bool
tvpi_term_equlas (tvpi_term_t t1, tvpi_term_t t2)
{
  return ((t1->sgn > 0 && t2->sgn > 0) || (t1->sgn < 0 && t2->sgn < 0)) &&
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
  return self->size;
}

void
tvpi_print_cst (FILE *f, tvpi_cst_t k)
{
  mpq_out_str (f, 10, *k);
}

void
tvpi_print_term (FILE *f, tvpi_term_t t)
{
  if (t->sgn < 0)
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

  if (c->sgn < 0) 
    { 
      mpq_neg (k1, k1);
      mpq_neg (k2, k2);
      op2 = c->op == LT ? ">" : ">=";
    }
  else
    op2 = c->op == LT ? "<" : "<=";

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
  r->sgn = t->sgn;
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
  r->sgn = -t->sgn;
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
  t->op = s ? LT : LEQ;
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
  return c->op == LT;
}

tvpi_term_t 
tvpi_get_term (tvpi_cons_t c)
{
  return c;
}

signed long int
tvpi_cst_get_si_num (tvpi_cst_t c)
{
  return mpz_get_si (mpq_numref (*c));
}

signed long int
tvpi_cst_get_si_den (tvpi_cst_t c)
{
  return mpz_get_si (mpq_denref (*c));
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
  r->op = c->op;
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
  
  r->op = c->op == LT ? LEQ : LT;
  r->cst = tvpi_negate_cst (c->cst);
  return r;
}



bool
tvpi_is_neg_cons (tvpi_cons_t c)
{
  return c->sgn < 0;
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
      else if (i == 0) return c1->op == LT || c2->op == LEQ;
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

  /* fprintf (stderr, "Resolving on %d c1: ", x); */
  /* tvpi_print_cons (stderr, c1); */
  /* fprintf (stderr, " with c2: "); */
  /* tvpi_print_cons (stderr, c2); */
  /* fprintf (stderr, "\n"); */

  assert (c1->var[0] == x || (IS_VAR(c1->var[1]) && c1->var[1] == x));
  assert (c2->var[0] == x || (IS_VAR(c2->var[1]) && c2->var[1] == x));

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

      /* re-establish index of the other variable */
      idx_o_c1 = c1->var [0] == x ? 1 : 0;
      idx_o_c2 = c2->var [0] == x ? 1 : 0;
    }

  /* compute idx of x in c1 and c2 */
  idx_x_c1 = 1 - idx_o_c1;
  idx_x_c2 = 1 - idx_o_c2;

  /** allocate the new constraint and it's constants */
  c = new_cons ();
  c->coeff = new_cst ();
  mpq_init (*c->coeff);
  c->cst = new_cst ();
  mpq_init (*c->cst);

  /* the resolvent is LT if either one of the arguments is LT */
  c->op = (c1->op == LEQ && c2->op == LEQ) ? LEQ : LT;

  
  /* special case when !IS_VAR(c1->var[1]) */
  if (!IS_VAR (c1->var [1]))
    {
      /* c1 only has x, c2 has x and some other variable */
      c->var [0] = c2->var[idx_o_c2];
      c->var [1] = -1;
      c->fst_coeff = NULL;
      
      if (idx_o_c2 == 0)
	{
	  c->sgn = c2->sgn;
	  
	  /* let c1: -x <= k, c2: z + n*x <= m 
	   * resolvent is   z <= |n|*k+m 
	   */
	  mpq_abs (*c->cst, *c2->coeff);
	  mpq_mul (*c->cst, *c->cst, *c1->cst);
	  mpq_add (*c->cst, *c->cst, *c2->cst);
	}
      else
	{ 
	  /* let c1: -x <= k, c2: x + n*y <= m
	   * resolvent is:  sgn(n) * y <= (m+k)/|n|
	   */
	  mpq_t tmp;
	  c->sgn = mpq_sgn (*c2->coeff);
	  
	  mpq_abs (*c->cst, *c2->coeff);
	  mpq_inv (*c->cst, *c->cst);

	  mpq_init (tmp);
	  mpq_add (tmp, *c1->cst, *c2->cst);
	  mpq_mul (*c->cst, *c->cst, tmp);
	  mpq_clear (tmp);
	}
      return c;
    }
  
  
  c->fst_coeff = new_cst ();
  mpq_init (*c->fst_coeff);
  
  /* variables of the new constraint */
  c->var[0] = c1->var[idx_o_c1];
  c->var[1] = c2->var[idx_o_c2];



  /* compute same_coeff flag */
  if (idx_x_c1 == 0)
    {
      if (idx_x_c2 == 0) same_coeff = 1;
      else
	/* note that we compare  c2->coeff with -coeff of x in c1 */
	same_coeff = (mpq_cmp_si (*c2->coeff, c1->sgn < 0 ? 1 : -1, 1) == 0);
    }
  else 
    {
      if (idx_x_c2 == 0)
	/* note that we compare c1->coeff with -coeff of x in c2 */
	same_coeff = (mpq_cmp_si (*c1->coeff, c2->sgn < 0 ? 1 : -1, 1) == 0);
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
  
  
  
  /* coefficient of c->var[0] is coeff(c1->var[idx_o_c1]) if
   * coefficients of x have same absolute value in c1 and c2, or
   * coeff (c1->var[idx_o_c1]) * coeff (c2->var[idx_x_c2])
   */
  
  if (idx_o_c1 == 0)
    mpq_set_si (*c->fst_coeff, c1->sgn < 0 ? -1 : 1, 1);
  else
    mpq_set (*c->fst_coeff, *c1->coeff);
  
  mpq_set (*c->cst, *c1->cst);
  
  if (!same_coeff && idx_x_c2 != 0)
    {
      /* multiply everything by coeff (c2->var[idx_x_c2]) */
      mpq_t v;
      mpq_init (v);
      mpq_abs (v, *c2->coeff);
      mpq_mul (*c->fst_coeff, *c->fst_coeff, v);
      mpq_mul (*c->cst, *c->cst, v);
      mpq_clear (v);
    }
  
  /* do the same thing for c->var[1] */
  if (idx_o_c2 == 0)
    mpq_set_si (*c->coeff, c2->sgn < 0 ? -1 : 1, 1);
  else
    mpq_set (*c->coeff, *c2->coeff);
  
  if (!same_coeff && idx_x_c1 != 0)
    {
      mpq_t v, u;
      mpq_init (v);
      mpq_init (u);

      mpq_abs (v, *c1->coeff);
      mpq_mul (*c->coeff, *c->coeff, v);

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

      assert (mpq_sgn (*c->fst_coeff) != 0 && "First coefficient becomes 0");
      
      c->var [1] = -1; 
      mpq_set_d (*c->coeff, 0.0); 
    }
  
  /* set the negative flag and absolute value of the first coefficient */
  c->sgn = mpq_sgn (*c->fst_coeff);
  if (c->sgn < 0)
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
 * Converts a constraint over rationals to constraint over integers.
 * Requires: r is TVPI
 */
tvpi_cons_t
tvpi_convert_q_to_z (tvpi_cons_t c)
{
  /* new constant */
  mpq_t k;

  /* input constraint is of the form 
   * +-x + (n/d)*y op z, where op is < or <=
   * 
   * over integers, it is equivalent to 
   * +-x + (n/d)*y <= (floor(d*z)-s)/d, where s=0 if op is <= and s=1 otherwise
   */

  /* k = 0/1 */
  mpq_init (k);

  /* if d != 1 */
  if (mpz_cmp_ui (mpq_denref (*c->coeff), 1) != 0)
    {
      mpz_t tmp;
     
      mpz_init (tmp);
      mpz_mul (tmp, mpq_denref (*c->coeff), mpq_numref (*c->cst));

      /* k = (floor(d*c->cst))/1 */
      mpz_fdiv_q (mpq_numref (k), tmp, mpq_denref (*c->cst));

      mpz_clear (tmp);
    }
  else
    mpz_fdiv_q (mpq_numref (k), mpq_numref (*c->cst), mpq_denref (*c->cst));

  
  if (c->op == LT)
    {
       mpz_sub_ui (mpq_numref (k), mpq_numref (k), 1); 
       c->op = LEQ;
    }
  
  /* divide by d if we multiplied by it in the previous step */
  if (mpz_cmp_ui (mpq_denref (*c->coeff), 1) != 0)
    {
      mpz_set (mpq_denref (k), mpq_denref (*c->coeff));
      /* if multiplied and divided by d, must canonicalize */
      mpq_canonicalize (k);
    }
  
  /* set the constant */
  mpq_set (*c->cst, k);
  /* clear temporary storage */
  mpq_clear (k);

  return c;
}



/**
 * Creates constraint in TVPI(Z) theory. 
 */
tvpi_cons_t
tvpi_z_create_cons (tvpi_term_t t, bool s, tvpi_cst_t k)
{
  tvpi_cons_t c;

  c = tvpi_create_cons (t, s, k);
  if (c == NULL) return NULL;
 
  return tvpi_convert_q_to_z (c);
}

/**
 * Negates a constraint in TVPI(Z) theory. 
 */
tvpi_cons_t
tvpi_z_negate_cons (tvpi_cons_t c)
{
  tvpi_cons_t r;
  
  r = tvpi_negate_cons (c);
  if (r == NULL) return NULL;
  
  return tvpi_convert_q_to_z (r);
}

tvpi_cons_t
tvpi_z_resolve_cons (tvpi_cons_t c1, tvpi_cons_t c2, int x)
{
  tvpi_cons_t r;
  
  r = tvpi_resolve_cons (c1, c2, x);
  if (r == NULL) return NULL;
  
  return tvpi_convert_q_to_z (r);
}

/**
 * Converts a constraint over rationals to constraint over integers.
 * Requires: r is UTVPI 
 */
tvpi_cons_t
tvpi_convert_uq_to_uz (tvpi_cons_t r)
{

  assert (!IS_VAR (r->var[1]) || 
	  (mpz_cmp_si (mpq_denref (*r->coeff), 1) == 0 &&
	   mpz_cmpabs_ui (mpq_numref (*r->coeff), 1) == 0));
  assert (mpz_cmp_si (mpq_denref (*r->cst), 1) == 0);

  if (r->op == LT)
    {
      /* using (n/d)-1 == (n-d)/d 
       * no need to canonicalize because  gcd(n,d)==1 IMPLIES gcd (n-d,d)==1
       */
      mpz_sub (mpq_numref (*r->cst), mpq_numref (*r->cst), mpq_denref (*r->cst));
      r->op = LEQ;
    }
  
  /* floor fractional constants */
  if (mpz_cmp_ui(mpq_denref (*r->cst), 1) != 0)
    {
      mpz_fdiv_q (mpq_numref (*r->cst), 
		  mpq_numref (*r->cst),
		  mpq_denref (*r->cst));
      mpz_set_ui (mpq_denref (*r->cst), 1);
    }
  
  
  return r;
}



/**
 * Creates constraint in UTVPI(Z) theory. 
 */
tvpi_cons_t
tvpi_uz_create_cons (tvpi_term_t t, bool s, tvpi_cst_t k)
{
  tvpi_cons_t c;
  /* check that the coefficient in t and constant k are integers */
  /* assert (!IS_VAR (t->var[1]) ||  */
  /* 	  (mpz_cmp_si (mpq_denref (*t->coeff), 1) == 0 && */
  /* 	   mpz_cmpabs_ui (mpq_numref (*t->coeff), 1) == 0)); */
  /* assert (mpz_cmp_si (mpq_denref (*k), 1) == 0); */

  c = tvpi_create_cons (t, s, k);
  if (c == NULL) return NULL;
 
  return tvpi_convert_uq_to_uz (c);
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
  
  return tvpi_convert_uq_to_uz (r);
}

tvpi_cons_t
tvpi_uz_resolve_cons (tvpi_cons_t c1, tvpi_cons_t c2, int x)
{
  tvpi_cons_t r;
  
  r = tvpi_resolve_cons (c1, c2, x);
  if (r == NULL) return NULL;
  
  return tvpi_convert_uq_to_uz (r);
}

/**
 * Ensures that theory has space for a variable
 */
static void
tvpi_ensure_capacity (tvpi_theory_t *t, int var)
{
  tvpi_list_node_t ***new_map;
  size_t new_size, i, j;

  /** all is good */
  if (var < t->size) return;

  /* need to re-allocate */
  new_size = var + 10;
  new_map = (tvpi_list_node_t***) 
    malloc (sizeof (tvpi_list_node_t**) * new_size);
  assert (new_map != NULL && "Unexpected out of memory");
  
  for (i = 0; i < new_size; i++)
    {
      new_map [i] = (tvpi_list_node_t**) 
	malloc (new_size * sizeof (tvpi_list_node_t*));
      assert (new_map [i] != NULL && "Unexpected out of memory");
      for (j = 0; j < new_size; j++)
	{
	  /* copy all the entries from the old map */
	  if (i < t->size && j < t->size)
	    new_map [i][j] = t->map [i][j];
	  else
	    /* set new entries to NULL */
	    new_map [i][j] = NULL;
	}
      /* free row i from the old map */
      if (i < t->size) free (t->map [i]);
    }

  /* at this point, all rows are freed, just kill the container */
  free (t->map);

  /* install a new map */
  t->map = new_map;
  t->size = new_size;
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
  
  /* initialize j */
  j = -1;
  
  var0 = c->var[0];
  /* if there is no second variable, use var0 */
  var1 = IS_VAR (c->var [1]) ? c->var[1] : var0;

  tvpi_ensure_capacity (t, var0 > var1 ? var0 : var1);
  
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
  if (i == 0 && j == 0 && p->cons->op == c->op)
    {
      return p->dd;
    }
  /* c precedes p->cons, insert before p->cons */
  else if (i > 0 || // c->coeff < p->cons->coeff
	   (i == 0 && j > 0) ||  // c->cst < p->cons->cst
	   (i == 0 && j == 0 && c->op == LT)) // c->op < p->cons->op
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
  else if (i < 0 || 
	   (i == 0 && j < 0) || 
	   (i == 0 && j == 0 && p->cons->op == LT))
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

  nc = c->sgn < 0 ? theory->base.negate_cons (c) : c;

  res = tvpi_get_dd (m, theory, nc);
  
  if (c->sgn < 0)
    tvpi_destroy_cons (nc);
  
  return  (c->sgn < 0 && res != NULL ? tdd_not (res) : res);
}


theory_t *
tvpi_create_theory (size_t vn)
{
  tvpi_theory_t * t;
  int i, j;
  
  t = (tvpi_theory_t*) malloc (sizeof (tvpi_theory_t));
  if (t == NULL) return NULL;

  t->size = vn;

  /* allocate and initialize the map */  
  t->map = (tvpi_list_node_t***) 
    malloc (sizeof (tvpi_list_node_t**) * t->size);
  if (t->map == NULL)
    {
      free (t);
      return NULL;
    }

  for (i = 0; i < t->size; i++)
    {
      t->map [i] = 
	(tvpi_list_node_t**) malloc (t->size * sizeof (tvpi_list_node_t*));
      /* XXX: handle malloc == NULL */
      for (j = 0; j < t->size; j++)
	t->map [i][j] = NULL;
    }
  

  if (one == NULL)
    {
      one = new_cst ();
      mpq_init (*one);
      mpq_set_si (*one, 1, 1);
    }
  
  if (none == NULL)
    {
      none = new_cst ();
      mpq_init (*none);
      mpq_set_si (*none, -1, 1);
    }
  
  
  t->base.create_int_cst =  (constant_t(*)(int)) tvpi_create_si_cst;
  t->base.create_rat_cst = (constant_t(*)(long,long)) tvpi_create_si_rat_cst;
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
  t->base.create_linterm_sparse = 
    (linterm_t(*)(int*,constant_t*,size_t))tvpi_create_term_sparse;
  t->base.create_linterm_sparse_si = 
    (linterm_t(*)(int*,int*,size_t))tvpi_create_term_sparse_si;

  
  t->base.term_size = (int(*)(linterm_t))tvpi_term_size;
  t->base.term_get_var = (int(*)(linterm_t,int))tvpi_term_get_var;
  t->base.term_get_coeff = (constant_t(*)(linterm_t,int))tvpi_term_get_coeff;
  
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
  t->base.cst_get_si_num = (signed long int(*)(constant_t))tvpi_cst_get_si_num;
  t->base.cst_get_si_den = (signed long int(*)(constant_t))tvpi_cst_get_si_den;
  
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

  for (i = 0; i < t->size; i++)
    {
      for (j = 0; j < t->size; j++)
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
  t->base.create_cons = 
    (lincons_t(*)(linterm_t,int,constant_t))tvpi_uz_create_cons;
  t->base.negate_cons = (lincons_t(*)(lincons_t))tvpi_uz_negate_cons;  
  t->base.resolve_cons = (lincons_t(*)(lincons_t,lincons_t,int))tvpi_uz_resolve_cons;


  return (theory_t*)t;
}

/**
 * Creates a theory TVPI(Z). The constraints are of the form +-d*x
 * +-n*y <= k, where d, n, k are in Z, and d and n have no common
 * divisors.
 *
 * XXX Unproven. Use at your own risk.
 */
theory_t*
tvpi_create_tvpiz_theory (size_t vn)
{
  tvpi_theory_t* t;
  
  t = (tvpi_theory_t*)tvpi_create_theory (vn);
  if (t == NULL) return NULL;
  

  /* update UTVPI(Z) specific functions.
   * The unique feature of UTVPI(Z) is that t < k is equivalent to t <= (k-1).
   * These following functions ensure that no strict inequalities are created.
   */
  t->base.create_cons = (lincons_t(*)(linterm_t,int,constant_t))tvpi_z_create_cons;
  t->base.negate_cons = (lincons_t(*)(lincons_t))tvpi_z_negate_cons;  
  t->base.resolve_cons = (lincons_t(*)(lincons_t,lincons_t,int))tvpi_z_resolve_cons;

  return (theory_t*)t;
}



#ifdef OCT_DEBUG
/**********************************************************************
 * Commented out. Used for debugging to compare against tdd-oct 
 * implementation.
 **********************************************************************/
oct_cons_t*
tvpi_to_oct (tvpi_cons_t c1)
{
  oct_cons_t* oct;
  
  oct = (oct_cons_t*) malloc (sizeof (oct_cons_t));

  oct->strict = (c1->op == LT);
  
  oct->term.var1 = c1->var[0];
  oct->term.var2 = c1->var[1];
  
  oct->term.coeff1 = c1->sgn < 0 ? -1 : 1;
  
  if (mpq_cmp_si (*c1->coeff, 1, 1) == 0)
    oct->term.coeff2 = 1;
  else  if (mpq_cmp_si (*c1->coeff, -1, 1) == 0)
    oct->term.coeff2 = -1;
  else
    assert (0 && "c1->coeff is not in {-1, 1}");

  oct->cst.type = OCT_INT;
  oct->cst.int_val = (int) mpz_get_si (mpq_numref (*c1->cst));

  return oct;
}

bool 
tvpi_oct_equals (tvpi_cons_t tvpi, oct_cons_t *oct)
{
  if (oct->term.var1 != tvpi->var [0] ||
      oct->term.var2 != tvpi->var [1]) return 0;
  
  if ((tvpi->sgn > 0 && oct->term.coeff1 == -1) ||
      (tvpi->sgn < 0 && oct->term.coeff1 == 1))
    return 0;


  if (mpq_cmp_si (*tvpi->coeff, oct->term.coeff2, 1) != 0) return 0;
  
  if ((tvpi->op == LT && !oct->strict) || (tvpi->op == LEQ && oct->strict))
    return 0;
  
  return mpq_cmp_si (*tvpi->cst, oct->cst.int_val, 1) == 0;
}


tvpi_cons_t
tvpi_debug_resolve_cons (tvpi_cons_t c1, tvpi_cons_t c2, int x)
{
  tvpi_cons_t tvpi;
  oct_cons_t *oc1, *oc2, *oct;
  
  tvpi = tvpi_uz_resolve_cons (c1, c2, x);
  
  oc1 = tvpi_to_oct (c1);
  assert (tvpi_oct_equals (c1, oc1));
  oc2 = tvpi_to_oct (c2);
  assert (tvpi_oct_equals (c2, oc2));
  oct = oct_resolve_int_cons (oc1, oc2, x);
  
  if (!tvpi_oct_equals (tvpi, oct))
    {

      fprintf (stderr, "TVPI: ");
      tvpi_print_cons (stderr, c1);
      fprintf (stderr, " ");
      tvpi_print_cons (stderr, c2);
      fprintf (stderr, " --> ");
      tvpi_print_cons (stderr, tvpi);
      fprintf (stderr, "\n");

      fprintf (stderr, "OCT: ");
      oct_print_cons (stderr, oc1);
      fprintf (stderr, " ");
      oct_print_cons (stderr, oc2);
      fprintf (stderr, " --> ");
      oct_print_cons (stderr, oct);
      fprintf (stderr, "\n");
      

      assert (0);
    }
  
  oct_destroy_lincons (oc1);
  oct_destroy_lincons (oc2);
  oct_destroy_lincons (oct);
  return tvpi;
}
#endif


#ifndef _TDD_H_
#define _TDD_H_

#include <stdio.h>
#include "cudd.h"

#ifndef __cplusplus
typedef int bool;
#endif


#ifdef __cplusplus
extern "C" {
#endif

/***********************************************************************
 * SIMPLE TYPES
 **********************************************************************/
typedef void* constant_t;
typedef void* linterm_t;
typedef void* lincons_t;

typedef void* qelim_context_t;

typedef DdNode tdd_node;

/* forward declaration so that we can define tdd_manager without
   defining theory */
typedef struct theory theory_t;

typedef struct tdd_manager tdd_manager;



/**
 * Theory inerface. Variables are represented by integers. Unless
 * otherwise mentioned, it is the user's responsibility to destroy
 * objects created by her.
 */
struct theory
{

  /* Create an integer constant. */
  constant_t (*create_int_cst) (int v);
  /** Create a rational constant */
  constant_t (*create_rat_cst) (int n, int d);
  /** Create a double constant */
  constant_t (*create_double_cst) (double v);

  /** Return -1*c */
  constant_t (*negate_cst) (constant_t c);

  /** Returns true if c is positive infinity */
  int (*is_pinf_cst)(constant_t c);
  /** Returns true if c is negative infinity */
  int (*is_ninf_cst)(constant_t c);

  /** Destroy a constant */
  void (*destroy_cst) (constant_t c);

  /** 
   * Create a linear term: the first argument is an array of variable
   * coefficients. the second argument is the size of the array of
   * coefficients.
   */
  linterm_t (*create_linterm)(int* coeffs, size_t n);

  /** Returns true if t1 is the same term as t2 */
  int (*term_equals)(linterm_t t1, linterm_t t2);

  /** 
   * Returns truee iff variable 'var' appears with a non-zero
   * coefficient in the term 't'.
   */
  int (*term_has_var) (linterm_t t, int var);

  /**
   * Returns true if there exists a variable v in the set var whose
   * coefficient in t is non-zero.

   * t is a term, var is represented as an array of booleans, 
   */
  int (*term_has_vars) (linterm_t t, int* vars);


  /* Returns the number of variables of the theory */
  size_t (*num_of_vars)(theory_t* self);

  /**
   * Returns >0 if t1 and t2 have a resolvent on variable x, 
   * Returns <0 if t1 and -t2 have a resolvent on variable x
   * Return 0 if t1 and t2 do not resolve.
   */
  int (*terms_have_resolvent) (linterm_t t1, linterm_t t2, int x);

  /** Returns -1*t */
  linterm_t (*negate_term) (linterm_t t);

  /** Returns a variable in vars that has a non-zero coefficient in t.
   *  Returns <0 if no such variable exists */
  int (*pick_var) (linterm_t t, int* vars);
  
  /** Reclaims resources allocated by t*/
  void (*destroy_term) (linterm_t t);


  /**
   * Creates a linear contraint t < k (if s is true) t<=k (if s is false)
   */
  lincons_t (*create_cons)(linterm_t t, int s, constant_t k);
  
  /**
   * Returns true if l is a strict constraint 
   */
  int (*is_strict)(lincons_t l);

  /**
   * get the term corresponding to the argument constraint
   */
  linterm_t (*get_term)(lincons_t l);
  
  /**
   * get the constant corresponding to the argument constraint
   */
  constant_t (*get_constant)(lincons_t l);


  /** 
   * Complements a linear constraint 
   */
  lincons_t (*negate_cons)(lincons_t l);  

  /**
   * Returns true if l is a negative constraint (i.e., the smallest
   * non-zero dimension has a negative coefficient.)
   */
  int (*is_negative_cons)(lincons_t l);

  /** used to be implies. If is_stronger_cons(l1, l2) then l1 implies l2 */
  int (*is_stronger_cons)(lincons_t l1, lincons_t l2);


  /**
   * Computes the resolvent of l1 and l2 on x. Returns NULL if there
   * is no resolvent.
   */
  lincons_t (*resolve_cons)(lincons_t l1, lincons_t l2, int x);
  

  /**
   * Reclaims resources allocated by l
   */
  void (*destroy_lincons)(lincons_t l);

  /**
   * Returns a copy of l
   */
  lincons_t (*dup_lincons)(lincons_t l);
  
  /**
   DD toDD (c)
   {
     // -- normalize c. 

   DD k = find(c);
   if (k != NULL) return k

   DD n = the weakest constraint t such that is_stronger_cons (t, c), or NULL
  
   if (n == NULL) 
     k = allocate new DD node for c
     associate k with c locally
     return k

   k = allocate new DD node right after n for c
   associate k with c locally
   return k;
   }

   also, see ddd-notes-ver2.txt somewhere in the same repository
  */
  tdd_node* (*to_tdd)(tdd_manager* m, lincons_t l);

  
  void (*print_lincons) (FILE* f, lincons_t l);

  /**
   * Prints debug information from the theory embedded in the manager.
   */
  void (*theory_debug_dump) (tdd_manager * tdd);

  /** Incremental Quantifier elimination */
  qelim_context_t* (*qelim_init)(tdd_manager *m, int* vars);
  void (*qelim_push)(qelim_context_t* ctx, lincons_t l);
  lincons_t (*qelim_pop)(qelim_context_t* ctx);
  tdd_node* (*qelim_solve)(qelim_context_t* ctx);
  void (*qelim_destroy_context)(qelim_context_t* ctx);
  
};


/***********************************************************************/
/* public interface */
/***********************************************************************/


#define tdd_not(X) Cudd_Not(X)


tdd_manager* tdd_init (DdManager *cudd, theory_t * t);
void tdd_quit (tdd_manager* tdd);

tdd_node* to_tdd(tdd_manager* m, lincons_t l);

tdd_node* tdd_new_var(tdd_manager* m, lincons_t l);
tdd_node* tdd_new_var_before (tdd_manager* m, tdd_node* v, lincons_t l);
tdd_node* tdd_new_var_after (tdd_manager* m, tdd_node* v, lincons_t l);

tdd_node *tdd_get_true (tdd_manager *m);
tdd_node *tdd_get_false (tdd_manager *m);

tdd_node* tdd_and (tdd_manager* m, tdd_node* n1, tdd_node* n2);
tdd_node* tdd_or (tdd_manager* m, tdd_node* n1, tdd_node* n2);
tdd_node* tdd_xor (tdd_manager* m, tdd_node* n1, tdd_node* n2);
tdd_node* tdd_ite (tdd_manager* m, tdd_node* n1, tdd_node* n2, tdd_node* n3);

tdd_node* tdd_exist_abstract (tdd_manager*, tdd_node*, int);
tdd_node* tdd_univ_abstract (tdd_manager*, tdd_node*, int);
tdd_node* tdd_resolve_elim (tdd_manager*, tdd_node*, linterm_t, 
			    lincons_t, int);
tdd_node* tdd_resolve (tdd_manager*, tdd_node*, 
		       linterm_t, lincons_t, lincons_t, int);
tdd_node* tdd_exist_abstract_v2 (tdd_manager*, tdd_node*, int*);

void tdd_manager_debug_dump (tdd_manager*);
int tdd_path_size (tdd_manager*, tdd_node*);

  void tdd_sanity_check (tdd_manager*);
  void tdd_node_sanity_check (tdd_manager*, tdd_node*);

  tdd_node *tdd_sat_reduce (tdd_manager *, tdd_node*, int);

/* tdd_node* tdd_and_resolve (tdd_manager *m, tdd_node *n1, int x);*/

#ifdef __cplusplus
}
#endif



#endif

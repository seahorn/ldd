#ifndef _THEORY_H_
#define _THEORY_H_


#include "cudd.h"

/***********************************************************************/
/* SIMPLE TYPES
/***********************************************************************/
typedef void* constant_t;
typedef void* linterm_t;
typedef void* lincons_t;
typedef int bool;

typedef void* qelim_context_t;

typedef DdNode tdd_node;

/* forward declaration to define the manager */
typedef struct theory theory_t;

/**
 * tdd manager 
 */
struct tdd_manager
{
  /** underlying cudd manager */
  DdManager * cudd;

  /** a map from DD variables to corresponding linear constraints */
  lincons_t* ddVars;

  /** size of ddVars array */
  size_t varsSize;

  theory_t* theory;
};

typedef struct tdd_manager tdd_manager;

/**
 * Theory inerface
 */

/**
 * Variables are represented by integers. 
 */

struct theory
{
  /** Create a constant from integer */
  constant_t (*create_int_cst) (int v);
  /** Create a rational constant */
  constant_t (*create_rat_cst) (int n, int d);
  /** Create a constant from double */
  constant_t (*create_double_cst) (double v);


  /** Returns true if c is positive infinity */
  bool (*is_pinf_cst)(constant_t c);
  /** Returns true if c is negative infinity */
  bool (*is_ninf_cst)(constant_t c);

  /** DISCUSS **/
  /** Create a linear term: This requires a discussion and depends
   ** on each individual theory. This may not needed by the DD!*/
  /* linterm_t (*create_linterm)(constant_t*, size_t n);*/

  /** Returns true if there exists a variable v in the array var whose
   ** coefficient in t is non-zero.
   **
   *  t is a term, var is an array of integers, and n is the size of
   *  var.
   **/
  bool (*term_has_var) (linterm_t t, int* var, size_t n);

  /**
   * Returns >0 if t1 and t2 have a resolvent on variable x, 
   * Returns <0 if t1 and -t2 have a resolvent on variable x
   * Return 0 if t1 and t2 do not resolve.
   */
  int (*terms_have_resolvent) (linterm_t t1, linterm_t t2, int x);

  /** Returns -1*t */
  linterm_t (*negate_term) (linterm_t t);
  
  /** Reclaims resources allocated by t*/
  void (*destroy_term) (linterm_t t);


  /**
   * Creates a linear contraint t < k (if s is true) t<=k (if s is false)
   */
  lincons_t (*create_cons)(linterm_t t, bool s, constant_t k);
  
  /**
   * Returns true if l is a strict constraint 
   */
  bool (*is_strict)(lincons_t l);

  linterm_t (*get_term)(lincons_t l);
  
  constant_t (*get_constant)(lincons_t l);


  /** 
   * Complements a linear constraint 
   */
  lincons_t (*negate_cons)(lincons_t l);  

  /** used to be implies. If is_stronger_cons(l1, l2) then l1 implies l2 */
  bool (*is_stronger_cons)(lincons_t l1, lincons_t l2);


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

  /** Incremental Quantifier elimination */
  qelim_context_t* (*qelim_init)(int *vars, size_t n);
  void (*qelim_push)(qelim_context_t* ctx, lincons_t l);
  void (*qelim_pop)(qelim_context_t* ctx);
  tdd_node* (*qelim_solve)(qelim_context_t* ctx);
  void (*qelim_destroy_context)(qelim_context_t* ctx);
  
};

void tdd_set_theory (tdd_manager *m, theory_t* t);
tdd_node* tdd_new_var(tdd_manager* m, lincons_t l);
tdd_node* tdd_new_var_before (tdd_manager* m, tdd_node* v, lincons_t l);

tdd_node* tdd_and (tdd_manager* m, tdd_node* n1, tdd_node* n2);

tdd_node* to_tdd(tdd_manager* m, lincons_t *l);

/**
 * tdd_manager functions
 */

/* typedef struct tdd_manager */
/* { */
/*   DdNode* (*tdd_new_var)(lincons_t l); */
/*   DdNode* (*tdd_new_var_before)(DdNode* v, lincons_t l); */
/* } tdd_manager; */


/** Functions to manipulate constants */

#endif

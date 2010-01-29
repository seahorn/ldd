#ifndef _LDD_H_
#define _LDD_H_

#include <stdio.h>
#include "cudd.h"

#ifndef __cplusplus
#ifndef SWIG
typedef int bool;
#endif
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

typedef DdNode LddNode;
typedef DdNode LddNodeset;

/* forward declaration so that we can define LddManager without
   defining theory */
typedef struct theory theory_t;

typedef struct LddManager LddManager;



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
  constant_t (*create_rat_cst) (long n, long d);
  /** Create a double constant */
  constant_t (*create_double_cst) (double v);


  /**
   * Returns numerator of a rational constant as a signed long
   */
  signed long int (*cst_get_si_num)(constant_t c);
  /**
   * Returns denominator of a rational constant as a signed long 
   */
  signed long int (*cst_get_si_den)(constant_t c);

  /** Duplicate a constant */
  constant_t (*dup_cst) (constant_t c);

  /** Return -1*c */
  constant_t (*negate_cst) (constant_t c);

  /** Returns true if c is positive infinity */
  int (*is_pinf_cst)(constant_t c);
  /** Returns true if c is negative infinity */
  int (*is_ninf_cst)(constant_t c);

  /* Sign of the constant. -1 if c < 0, 1 if c > 0, 0 if c = 0 */
  int (*sgn_cst)(constant_t c);

  /** Destroy a constant */
  void (*destroy_cst) (constant_t c);

  /** Returns c1+c3 */
  constant_t (*add_cst) (constant_t c1, constant_t c2);

  /** Returns c1*c2 */
  constant_t (*mul_cst) (constant_t c1, constant_t c2);
  

  /** 
   * Create a linear term: the first argument is an array of variable
   * coefficients. the second argument is the size of the array of
   * coefficients.
   */
  linterm_t (*create_linterm)(int* coeffs, size_t n);

  /**
   * Returns the size, number of variables with non-zero coefficients, of a term
   */
  int (*term_size)(linterm_t t);
  
  /**
   * Returns ith variable with a non-zero coefficient.
   * Requires:  0 <= i <= term_size (t)
   */
  int (*term_get_var)(linterm_t t, int i);
  
  /**
   * Returns the coefficient of the ith variable with a non-zero
   * coefficient.  Requires: 0 <= i <= term_size (t)
   */  
  constant_t (*term_get_coeff)(linterm_t, int i);

  /**
   * Creates a term coeff[0]*var[0] + ... + coeff[n]*var[n]. An
   * alternative to create_linterm.
   *
   * Requires: var is sorted; length of var = length of coeff = n;   
   */
  linterm_t (*create_linterm_sparse_si)(int* var, int* coeff, size_t n);
  linterm_t (*create_linterm_sparse)(int* var, constant_t* coeff, size_t n);


  /** Duplicate a term */
  linterm_t (*dup_term) (linterm_t t);

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
   * For each variable x_i that has a non-zero coefficient in the
   * constraint l, increments occurs[i]. occurs must be large enough
   * to accommodate all variables in l.
   */
  void (*var_occurrences)(lincons_t l, int* occurs);

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
   * Returns an LDD corresponding to a constraint 
   */
  LddNode* (*to_ldd)(LddManager* m, lincons_t l);

  /**
   * Substitute (t + c) for x in l. 
   */
  LddNode* (*subst)(LddManager* m, lincons_t l, 
		   int x, linterm_t t, constant_t c);
  
  /**
   * Substitute (t + c + epsilon) for x in l, where epsilon is
   * an arbitrary small value */
  LddNode* (*subst_pluse)(LddManager *m, lincons_t l,
			  int x, linterm_t t, constant_t c);
  
  /**								
   * Substitute negative infinity for x in l 
   */
  LddNode* (*subst_ninf)(LddManager *m, lincons_t l, int x);
  
  
  
  void (*print_lincons) (FILE* f, lincons_t l);

  /**
   * Prints debug information from the theory embedded in the manager.
   */
  void (*theory_debug_dump) (LddManager * tdd);

  /** Incremental Quantifier elimination */
  qelim_context_t* (*qelim_init)(LddManager *m, int* vars);
  void (*qelim_push)(qelim_context_t* ctx, lincons_t l);
  lincons_t (*qelim_pop)(qelim_context_t* ctx);
  LddNode* (*qelim_solve)(qelim_context_t* ctx);
  void (*qelim_destroy_context)(qelim_context_t* ctx);



};


/***********************************************************************/
/* public interface */
/***********************************************************************/


#define Ldd_Not(X) Cudd_Not(X)
#define Ldd_NodeToNodeset(X) ((LddNodeset*)X)

#define Ldd_Ref(X) Cudd_Ref(X)
#define Ldd_Deref(X) Cudd_Deref(X)
#define Ldd_RecursiveDeref(T,X) Cudd_IterDerefBdd(Ldd_GetCudd(T),X)

#define Ldd_NodesetRef(X) Cudd_Ref(X)
#define Ldd_NodesetDeref(X) Cudd_Deref(X)
#define Ldd_NodesetRecursiveDeref(T,X) Cudd_IterDerefBbd(T->cudd,X)

#define Ldd_T(X) Cudd_T(X)
#define Ldd_E(X) Cudd_E(X)
#define Ldd_Regular(X) Cudd_Regular(X)
LddManager* Ldd_Init (DdManager *cudd, theory_t * t);
void Ldd_Quit (LddManager* tdd);

LddNode* Ldd_FromCons(LddManager* m, lincons_t l);

LddNode* Ldd_NewVar(LddManager* m, lincons_t l);
LddNode* Ldd_NewVarAtTop (LddManager* m, lincons_t l);
LddNode* Ldd_NewVarBefore (LddManager* m, LddNode* v, lincons_t l);
LddNode* Ldd_NewVarAfter (LddManager* m, LddNode* v, lincons_t l);

LddNode *Ldd_GetTrue (LddManager *m);
LddNode *Ldd_GetFalse (LddManager *m);

LddNode* Ldd_And (LddManager* m, LddNode* n1, LddNode* n2);
LddNode* Ldd_Or (LddManager* m, LddNode* n1, LddNode* n2);
LddNode* Ldd_Xor (LddManager* m, LddNode* n1, LddNode* n2);
LddNode* Ldd_Ite (LddManager* m, LddNode* n1, LddNode* n2, LddNode* n3);

LddNode* Ldd_ExistAbstract (LddManager*, LddNode*, int);
LddNode* Ldd_UnivAbstract (LddManager*, LddNode*, int);
LddNode* Ldd_ResolveElim (LddManager*, LddNode*, linterm_t, 
			    lincons_t, int);
LddNode* Ldd_Resolve (LddManager*, LddNode*, 
		       linterm_t, lincons_t, lincons_t, int);
LddNode* Ldd_ExistAbstractV2 (LddManager*, LddNode*, int*);

void Ldd_ManagerDebugDump (LddManager*);
int Ldd_PathSize (LddManager*, LddNode*);
  
void Ldd_SanityCheck (LddManager*);
void Ldd_NodeSanityCheck (LddManager*, LddNode*);

LddNode *Ldd_SatReduce (LddManager *, LddNode*, int);
bool Ldd_IsSat (LddManager *, LddNode*);
int Ldd_UnsatSize (LddManager *, LddNode*);
theory_t *Ldd_SyntacticImplicationTheory (theory_t *t);
void Ldd_VarOccurrences (LddManager *, LddNode *, int*);
LddNode *Ldd_BddExistAbstract (LddManager*,LddNode*,LddNode*);
LddNode *Ldd_TermsWithVars (LddManager*, int*);
LddNode *Ldd_OverAbstract (LddManager *,LddNode*,int*);
void Ldd_SupportVarOccurrences (LddManager*,LddNode*,int*);
LddManager * Ldd_BddlikeManager (LddManager *);
LddNode * Ldd_ExistAbstractV3 (LddManager*, LddNode*, int);
LddNode * Ldd_MvExistAbstract (LddManager*, LddNode *, int * , size_t );
LddNode * Ldd_BoxExtrapolate (LddManager*, LddNode*, LddNode*);
LddNode* Ldd_TermReplace (LddManager*, LddNode*, linterm_t, linterm_t, constant_t, constant_t, constant_t);
LddNode* Ldd_TermMinmaxApprox (LddManager*, LddNode*);
LddNode* Ldd_TermConstrain (LddManager*, LddNode*, 
				linterm_t, linterm_t, constant_t);
/* LddNodeset* Ldd_empty_nodeset (LddManager*); */
LddNodeset* Ldd_NodesetUnion (LddManager*, LddNodeset*, LddNodeset*);
LddNodeset* Ldd_NodesetAdd (LddManager*, LddNodeset*, LddNode*);
int Ldd_PrintMinterm(LddManager*, LddNode*);

DdManager * Ldd_GetCudd (LddManager *);
  lincons_t Ldd_GetCons (LddManager*, LddNode*);
/* LddNode* Ldd_and_resolve (LddManager *m, LddNode *n1, int x);*/

#ifdef __cplusplus
}
#endif



#endif

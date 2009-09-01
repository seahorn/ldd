#include "util.h"
#include "cudd.h"
#include "tdd.h"
#include "tvpi.h"

#include <stdio.h>

/**
 * A structure describing a test case. Each testcase is of the form C1
 * && ... && Cn => C where Ci's and C are constraints.
 */
typedef struct testcase {
  int varnum;
  int consnum;
  int **ante;
  int *cons;
} testcase_t;

DdManager *cudd = NULL;
tdd_manager* tdd = NULL;
theory_t * theory = NULL;

tdd_node *create_cons(testcase_t *tc,int *arg)
{
  constant_t c = theory->create_int_cst(arg[tc->varnum]);
  linterm_t t = theory->create_linterm (arg,tc->varnum);
  lincons_t l = theory->create_cons (t, 0, c);
  tdd_node *d = to_tdd (tdd, l);
  Cudd_Ref (d);
  return d;
}

void test(testcase_t *tc)
{
  printf ("Creating the world...\n");
  cudd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);
  theory = tvpi_create_theory (tc->varnum);
  tdd = tdd_init (cudd, theory);
  
  //create antecedent
  tdd_node *ante = NULL;
  int i;
  for(i = 0;i < tc->consnum;++i) {
    tdd_node *d = create_cons(tc,tc->ante[i]);
    ante = (ante == NULL) ? d : tdd_and(tdd,ante,d);
  }

  //create consequent
  tdd_node *cons = create_cons(tc,tc->cons);

  //create negation implication
  tdd_node *impl = tdd_not(tdd_or (tdd, tdd_not (ante), cons));

  //existential abstraction
  tdd_node *abs = impl;
  for(i = 0;i < tc->varnum;++i) {
    abs = tdd_exist_abstract (tdd, abs, i);
  }
  abs = tdd_not(abs);

  //check for validity
  assert(abs == Cudd_ReadOne(cudd));

  //cleanup
  printf ("Destroying the world...\n");
  tdd_quit (tdd);
  tvpi_destroy_theory (theory);
  Cudd_Quit (cudd);
}

int main(void)
{
  testcase_t tc1;
  tc1.varnum = 3;
  tc1.consnum = 2;
  tc1.ante = (int**)malloc(2 * sizeof(int*));
  int a11[] = {1,-1,0,5};
  int a12[] = {0,1,-1,10};
  tc1.ante[0] = a11;
  tc1.ante[1] = a12;
  int c1[] = {1,0,-1,15};
  tc1.cons = c1;
  test(&tc1);
  return 0;
}

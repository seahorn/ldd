#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cassert>
#include <ctime>

#include "util.h"
#include "cudd.h"
#include "tdd.h"
#include "tdd-ddd.h"

/**
 * This program creates a set of constraints that correspond to a
 * diamond-shaped program. At each meet-point, two new freash
 * variables X and Y are introduced. New constraints on X and Y are
 * introduced so that an invariant of the form X - Y >= K is
 * maintained. 
 *
 * The program accepts a number of inputs:
 * -- depth <K>: the number of diamonds in the program generated
 * -- branch <K>: the branching factor
 * --unsat: if the problem should be unsatisfiable
 */

/*********************************************************************/
//global variables -- store command line options
/*********************************************************************/
//command line options
int depth = 0;
int branch = 0;
bool unsat = false;

//other data structures
DdManager *cudd;
tdd_manager *tdd;
theory_t *theory;

/*********************************************************************/
//return a random integer between min (inclusive) and max (exclusive)
/*********************************************************************/
int Rand(int min,int max)
{
  if(min >= max) {
    printf("ERROR: can't generate a random number between %d and %d!!\n",min,max);
    exit(0);
  }
  return min + (rand() % (max - min));
}

/*********************************************************************/
//process inputs -- also print inputs for later reference
/*********************************************************************/
void ProcessInputs(int argc,char *argv[])
{
  printf("Command Line:");
  for(int i = 0;i < argc;++i) {
    printf(" %s",argv[i]);
    if(!strcmp(argv[i],"--depth") && i < argc-1) {
      depth = atoi(argv[i+1]);
    }
    if(!strcmp(argv[i],"--branch") && i < argc-1) {
      branch = atoi(argv[i+1]);
    }
    if(!strcmp(argv[i],"--unsat")) unsat = true;
  }
  printf("\n");
  printf("depth = %d branch = %d unsat = %s\n",
         depth,branch,unsat ? "true" : "false");
  if(depth <= 0) {
    printf("ERROR: depth must be greater than zero!\n");
    exit(0);
  }
}

/*********************************************************************/
//create all kinds of managers
/*********************************************************************/
void CreateManagers()
{
  cudd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);
  theory = ddd_create_int_theory (2 * depth);
  tdd = tdd_init (cudd, theory);  
}

/*********************************************************************/
//create and return the tdd_node for the constraint X-Y <= K
/*********************************************************************/
tdd_node *ConsToTdd(int x,int y,int k)
{
  constant_t cst = theory->create_int_cst(k);
  int *cf = (int*)malloc(2 * depth * sizeof(int));
  memset(cf,0,2 * depth * sizeof(int));
  cf[x] = 1;
  cf[y] = -1;
  linterm_t term = theory->create_linterm(cf,2 * depth);
  free(cf);
  lincons_t cons = theory->create_cons(term,0,cst);
  theory->destroy_cst(cst);
  theory->destroy_term(term);
  tdd_node *res = to_tdd(tdd,cons);
  theory->destroy_lincons(cons);
  return res;
}

/*********************************************************************/
//generate all the constraints and then quantify out all but the last
//two fresh variables
/*********************************************************************/
void GenAndSolve1()
{
  //the constant bound K for invariants. the invariant at the join
  //points after each diamond is X - Y >= K
  int bound = rand();

  tdd_node *node = tdd_get_true(tdd);
  Cudd_Ref(node);

  for(int d = 0;d < depth;++d) {
    //fresh variables
    int v1 = 2 * d,v2 = 2 * d + 1;

    //if at the start of the program
    if(d == 0) {
      printf("level = 0\n");
      //create constraint v1 - v2 <= bound
      tdd_node *node1 = ConsToTdd(v1,v2,bound);
      Cudd_Ref(node1);
      tdd_node *node2 = tdd_and(tdd,node,node1);
      Cudd_Ref(node2);
      Cudd_RecursiveDeref(cudd,node);
      Cudd_RecursiveDeref(cudd,node1);
      node = node2;
      continue;
    }

    //get the branching factor
    int bfac = Rand(0,branch + 1);
    printf("level = %d\tbranching = %d\n",d,bfac);
    //get the previous variables
    int pv1 = 2 * (d - 1),pv2 = 2 * d - 1;
    //disjunctive choices at the start of this diamond
    tdd_node *choice = tdd_get_false(tdd);
    Cudd_Ref(choice);
    //create branches
    for(int i = 0;i < bfac;++i) {
      //create a random slippage
      int slip = rand();
      //create two constraints pv1 <= v1 - slip and pv2 >= v2 +
      //slip. together with the previous invariant v1 - v2 <= bound,
      //this ensures the new invariant pv1 - pv2 <= bound.
      tdd_node *node1 = ConsToTdd(pv1,v1,-slip);
      Cudd_Ref(node1);
      tdd_node *node2 = ConsToTdd(v2,pv2,-slip);
      Cudd_Ref(node2);
      tdd_node *node3 = tdd_and(tdd,node1,node2);
      Cudd_Ref(node3);
      Cudd_RecursiveDeref(cudd,node1);
      Cudd_RecursiveDeref(cudd,node2);
      tdd_node *node4 = tdd_or(tdd,choice,node3);
      Cudd_Ref(node4);
      Cudd_RecursiveDeref(cudd,choice);
      Cudd_RecursiveDeref(cudd,node3);
      choice = node4;
    }
    
    //add the choice
    tdd_node *node1 = tdd_and(tdd,node,choice);
    Cudd_Ref(node1);
    Cudd_RecursiveDeref(cudd,node);
    Cudd_RecursiveDeref(cudd,choice);
    node = node1;
  }

  //now quantify out all elements
  for(int i = 0;i < 2 * depth;++i) {
    tdd_node *tmp = tdd_exist_abstract (tdd, node, i);
    Cudd_Ref (tmp);
    Cudd_RecursiveDeref (cudd, node);
    node = tmp;
  }

  //check if the result is correct
  if(unsat) {
    if(node == Cudd_ReadLogicZero (cudd))
      printf("GOOD: result is UNSAT as expected!\n");
    else
      printf("ERROR: result is SAT, UNSAT expected!\n");
  } else {
    if(node == Cudd_ReadOne (cudd))
      printf("GOOD: result is SAT as expected!\n");
    else
      printf("ERROR: result is UNSAT, SAT expected!\n");
  }
}

/*********************************************************************/
//the main procedure
/*********************************************************************/
int main(int argc,char *argv[])
{
  srand(time(NULL));
  ProcessInputs(argc,argv);
  CreateManagers();
  GenAndSolve1();

  return 0;
}

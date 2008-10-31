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
int qelimInt = 0;
size_t repeat = 1;
size_t disj = 1;
bool unsat = false;
bool qelim2 = false;

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
//display usage
/*********************************************************************/
void Usage(char *cmd)
{
  printf("Usage : %s <options>\n",cmd);
  printf("Options:\n");
  printf("\t--help|-h : display usage and exit\n");
  printf("\t--depth [number of diamonds]\n");
  printf("\t--branch <K> : K = maximum branching factor\n");
  printf("\t--qelimInt <K> : do QELIM after every K diamonds\n");
  printf("\t--repeat <K> : repeat experiment K (<= 1000) times\n");
  printf("\t--disj <K> : ensure that invariants have K disjuncts\n");
  printf("\t--unsat : generate unsatisfiable constraints\n");
  printf("\t--qelim2 : use QELIM algorithm that relies on a theory solver\n");
}

/*********************************************************************/
//process inputs -- also print inputs for later reference
/*********************************************************************/
void ProcessInputs(int argc,char *argv[])
{
  //display command line
  printf("Command Line:");
  for(int i = 0;i < argc;++i) {
    printf(" %s",argv[i]);
  }
  printf("\n");

  //check for empty command line
  if(argc == 1) {
    Usage(argv[0]);
    exit(1);
  }

  //process command line arguments
  for(int i = 1;i < argc;++i) {
    if(!strcmp(argv[i],"--help") || !strcmp(argv[1],"-h")) {
      Usage(argv[0]);
      exit(0);
    } else if(!strcmp(argv[i],"--depth") && i < argc-1) {
      depth = atoi(argv[++i]);
    }
    else if(!strcmp(argv[i],"--branch") && i < argc-1) {
      branch = atoi(argv[++i]);
    }
    else if(!strcmp(argv[i],"--qelimInt") && i < argc-1) {
      qelimInt = atoi(argv[++i]);
    }
    else if(!strcmp(argv[i],"--repeat") && i < argc-1) {
      repeat = atoi(argv[++i]);
    }
    else if(!strcmp(argv[i],"--disj") && i < argc-1) {
      disj = atoi(argv[++i]);
    }
    else if(!strcmp(argv[i],"--unsat")) unsat = true;
    else if(!strcmp(argv[i],"--qelim2")) qelim2 = true;
    else {
      Usage(argv[0]);
      exit(1);
    }
  }

  //sanity check on various option values
  if(depth <= 0) {
    printf("ERROR: depth must be greater than zero!\n");
    exit(0);
  }
  if(qelimInt < 1) qelimInt = depth;
  if(repeat > 1000) {
    printf("ERROR: can only repeat at most 1000 times!\n");
    exit(1);
  }
  if(disj < 1 || disj > 1000) {
    printf("ERROR: can have at least 1 and at most 1000 disjuncts in invariants!\n");
    exit(1);
  }
  
  //display final options
  printf("depth = %d branch = %d qelimInt = %d repeat = %d "
         "unsat = %s qelim2 = %s\n",
         depth,branch,qelimInt,repeat,unsat ? "true" : "false",
         qelim2 ? "true" : "false");
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
//create all kinds of managers
/*********************************************************************/
void DestroyManagers()
{
  ddd_destroy_theory(theory);
  tdd_quit(tdd);
  Cudd_Quit(cudd);
}

/*********************************************************************/
//create and return the tdd_node for the constraint X-Y <= K
/*********************************************************************/
tdd_node *ConsToTdd(int x,int y,int k)
{
#ifdef DEBUG
  printf("adding x%d - x%d <= %d\n",x,y,k);
#endif
  constant_t cst = theory->create_int_cst(k);
  int *cf = (int*)malloc(2 * depth * sizeof(int));
  memset(cf,0,2 * depth * sizeof(int));
  cf[x] = 1;
  cf[y] = -1;
  linterm_t term = theory->create_linterm(cf,2 * depth);
  free(cf);
  lincons_t cons = theory->create_cons(term,0,cst);
  tdd_node *res = to_tdd(tdd,cons);
  theory->destroy_lincons(cons);
  return res;
}

/*********************************************************************/
//quantify out all variables from min to max-1 from node and return
//the result. deref node.
/*********************************************************************/
tdd_node *Qelim(tdd_node *node,int min,int max)
{
  int *vars = new int [2 * depth];
  memset(vars,0,2*depth);

  //now quantify out elements if using qelim1, or set the elements of
  //vars to 1 if using qelim2
  for(int i = min;i < max;++i) {
    if(qelim2) vars[i] = 1;
    else {
      tdd_node *tmp = tdd_exist_abstract (tdd, node, i);
      Cudd_Ref (tmp);
      Cudd_RecursiveDeref (cudd, node);
      node = tmp;
    }
  }

  //quantify, if using qelim2
  if(qelim2) {
    tdd_node *tmp = tdd_exist_abstract_v2 (tdd, node, vars);
    Cudd_Ref (tmp);
    Cudd_RecursiveDeref (cudd, node);
    node = tmp;
  }

  //cleanup and return
  delete [] vars;
  return node;
}

/*********************************************************************/
//generate all the constraints and then quantify out all but the last
//two fresh variables
/*********************************************************************/
void GenAndSolve()
{
  //the constant bounds for invariants. there are as many bounds as
  //the number of disjuncts in the invariant. the invariant at the
  //join points after each diamond is ||( X - Y <= K_i)
  int *bounds = new int[disj];
  for(size_t i = 0;i < disj;++i) bounds[i] = Rand(-1000,1000);

  //the depth at which we are going to generate the UNSAT clause, if
  //any
  int target = Rand(0,depth);
#ifdef DEBUG
  printf("target = %d\n",target);
#endif

  //the minimum variable from which to start qelim
  int minVar = 0;

  tdd_node *node = tdd_get_true(tdd);
  Cudd_Ref(node);

  for(int d = 0;d < depth;++d) {
    //fresh variables
    int v1 = 2 * d,v2 = 2 * d + 1;

    //generate a constraint that makes the whole system unsatisfiable,
    //if needed
    if(unsat && d == target) {
      for(size_t i = 0;i < disj;++i) {
        tdd_node *node1 = ConsToTdd(v2,v1,-bounds[i]-1);
        Cudd_Ref(node1);
        tdd_node *node2 = tdd_and(tdd,node,node1);
        Cudd_Ref(node2);
        Cudd_RecursiveDeref(cudd,node);
        Cudd_RecursiveDeref(cudd,node1);
        node = node2;
      }
#ifdef DEBUG
      printf ("node is:\n");
      Cudd_PrintMinterm (cudd, node);
#endif
    }

    //if at the start of the program
    if(d == 0) {
#ifdef DEBUG
      printf("level = 0\n");
#endif
      //generate the top-level disjunctive invariant 
      tdd_node *choice = tdd_get_false(tdd);
      Cudd_Ref(choice);
      for(size_t i = 0;i < disj;++i) {
        //create constraint v1 - v2 <= bound
        tdd_node *node1 = ConsToTdd(v1,v2,bounds[i]);
        Cudd_Ref(node1);
        tdd_node *node2 = tdd_or(tdd,choice,node1);
        Cudd_Ref(node2);
        Cudd_RecursiveDeref(cudd,choice);
        Cudd_RecursiveDeref(cudd,node1);
        choice = node2;
      }
      tdd_node *node1 = tdd_and(tdd,node,choice);
      Cudd_Ref(node1);
      Cudd_RecursiveDeref(cudd,node);
      Cudd_RecursiveDeref(cudd,choice);
      node = node1;
#ifdef DEBUG
      printf ("node is:\n");
      Cudd_PrintMinterm (cudd, node);
#endif
      continue;
    }

    //get the branching factor
    int bfac = Rand(1,branch + 1);
#ifdef DEBUG
    printf("level = %d\tbranching = %d\n",d,bfac);
#endif
    //get the previous variables
    int pv1 = 2 * (d - 1),pv2 = 2 * d - 1;
    //disjunctive choices at the start of this diamond
    tdd_node *choice = tdd_get_false(tdd);
    Cudd_Ref(choice);
    //create branches
    for(int i = 0;i < bfac;++i) {
      //create a random positive slippage
      int slip = Rand(0,1000);
      //create two constraints v1 <= pv1 - slip and v2 >= pv2 +
      //slip. together with the previous invariant pv1 - pv2 <= bound,
      //this ensures the new invariant v1 - v2 <= bound.
      tdd_node *node1 = ConsToTdd(v1,pv1,-slip);
      Cudd_Ref(node1);
      tdd_node *node2 = ConsToTdd(pv2,v2,-slip);
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
#ifdef DEBUG
    printf ("choice is:\n");
    Cudd_PrintMinterm (cudd, choice);
#endif
    tdd_node *node1 = tdd_and(tdd,node,choice);
    Cudd_Ref(node1);
    Cudd_RecursiveDeref(cudd,node);
    Cudd_RecursiveDeref(cudd,choice);
    node = node1;
#ifdef DEBUG
    printf ("node is:\n");
    Cudd_PrintMinterm (cudd, node);
#endif

    //quantify if we have completed the next interval
    if(d > 0 && (d % qelimInt) == 0) {
      node = Qelim(node,minVar,v1);
      minVar = v1;
    }
  }

  //quantify
  node = Qelim(node,minVar,2 * depth);

  //check if the result is correct
  if(unsat) {
    if(node == Cudd_ReadLogicZero (cudd))
      printf("GOOD: result is UNSAT as expected!\n");
    else {
      printf("ERROR: result is SAT, UNSAT expected!\n");
      exit(1);
    }
  } else {
    if(node == Cudd_ReadOne (cudd))
      printf("GOOD: result is SAT as expected!\n");
    else {
      printf("ERROR: result is UNSAT, SAT expected!\n");
      exit(1);
    }
  }

  //cleanup
  delete [] bounds;
}

/*********************************************************************/
//the main procedure
/*********************************************************************/
int main(int argc,char *argv[])
{
  srand(time(NULL));
  ProcessInputs(argc,argv);
  for(size_t i = 0;i < repeat;++i) {
    CreateManagers();
    GenAndSolve();
    DestroyManagers();
  }
  return 0;
}

/*********************************************************************/
//end of diamond.cpp
/*********************************************************************/

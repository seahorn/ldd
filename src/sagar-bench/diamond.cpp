#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cassert>
#include <ctime>

//#define DEBUG

#include "util.h"
#include "cudd.h"
#include "tdd.h"
#ifdef DEBUG
#include "tddInt.h"
#endif
#include "tdd-ddd.h"
#include "tdd-oct.h"
#include "tdd-tvpi.h"

/**
 * This program creates a set of constraints that correspond to a
 * diamond-shaped program. At each meet-point, two new freash
 * variables X and Y are introduced. New constraints on X and Y are
 * introduced so that an invariant of the form X - Y >= K is
 * maintained. 
 *
 * The program accepts a number of inputs:
 * --depth <K>: the number of diamonds in the program generated
 * --branch <K>: the branching factor
 * --unsat: if the problem should be unsatisfiable
 */

/*********************************************************************/
//global variables -- store command line options
/*********************************************************************/
//command line options
int depth = 0;
int branch = 1;
size_t repeat = 1;
size_t disj = 1;
size_t varNum = 1;
int predNum = 0;
bool unsat = false;
bool qelim2 = false;
bool compInv = false;
enum TddType { DIA_DDD, DIA_OCT, DIA_TVPI } 
  tddType = DIA_DDD,consType = DIA_DDD;
bool summary = false;
bool image = false;

//other data structures
int totalVarNum = 0;
int *varSet = NULL;
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
  printf("\t--depth <number of diamonds + 1>\n");
  printf("\t--branch <K> : K = maximum branching factor\n");
  printf("\t--repeat <K> : repeat experiment K (<= 1000) times\n");
  printf("\t--disj <K> : ensure that invariants have K disjuncts\n");
  printf("\t--vars <K> : use K pairs of fresh variables at each step\n");
  printf("\t--preds <K> : use K predicates\n");
  printf("\t--unsat : generate unsatisfiable constraints\n");
  printf("\t--qelim2 : use QELIM algorithm that relies on a theory solver\n");
  printf("\t--oct : use octagon theory\n");
  printf("\t--octCons : use octagon constraints\n");
  printf("\t--tvpi : use TVPI theory\n");
  printf("\t--tvpiCons : use TVPI constraints\n");
  printf("\t--compInv : enable propositionally complex invariants\n");
  printf("\t--summary : whether to compute summaries\n");
  printf("\t--image : whether to do image computation\n");
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
    else if(!strcmp(argv[i],"--repeat") && i < argc-1) {
      repeat = atoi(argv[++i]);
    }
    else if(!strcmp(argv[i],"--disj") && i < argc-1) {
      disj = atoi(argv[++i]);
    }
    else if(!strcmp(argv[i],"--vars") && i < argc-1) {
      varNum = atoi(argv[++i]);
    }
    else if(!strcmp(argv[i],"--preds") && i < argc-1) {
      predNum = atoi(argv[++i]);
    }
    else if(!strcmp(argv[i],"--unsat")) unsat = true;
    else if(!strcmp(argv[i],"--qelim2")) qelim2 = true;
    else if(!strcmp(argv[i],"--oct")) tddType = DIA_OCT;
    else if(!strcmp(argv[i],"--octCons")) consType = DIA_OCT;
    else if(!strcmp(argv[i],"--tvpi")) tddType = DIA_TVPI;
    else if(!strcmp(argv[i],"--tvpiCons")) consType = DIA_TVPI;
    else if(!strcmp(argv[i],"--compInv")) compInv = true;
    else if(!strcmp(argv[i],"--summary")) summary = true;
    else if(!strcmp(argv[i],"--image")) image = true;
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
  if(repeat > 1000) {
    printf("ERROR: can only repeat at most 1000 times!\n");
    exit(1);
  }
  if(disj < 1 || disj > 1000) {
    printf("ERROR: can have at least 1 and at most 1000 disjuncts in invariants!\n");
    exit(1);
  }
  if(varNum < 1 || varNum > 1000) {
    printf("ERROR: can have at least 1 and at most 1000 fresh variables at each step!\n");
    exit(1);
  }
  if(varNum < 0 || varNum > 100) {
    printf("ERROR: can have at least 0 and at most 100 predicates!\n");
    exit(1);
  }
  if(consType == DIA_OCT && tddType == DIA_DDD) {
    printf("ERROR: cannot use DDD theory with octagon constraints!\n");
    exit(1);
  }
  if(consType == DIA_TVPI && tddType != DIA_TVPI) {
    printf("ERROR: must use TVPI theory with TVPI constraints!\n");
    exit(1);
  }
  if((summary || image) && depth < 2) {
    printf("ERROR: must have at least one diamond to compute image or summary!\n");
    exit(1);
  }
  if(summary && image) {
    printf("ERROR: cannot compute both summary and image!\n");
    exit(1);
  }
  if(predNum > 0 && !summary && !image) {
    printf("ERROR: must compute summary or image with predicate abstraction!\n");
    exit(1);
  }

  //compute total number of numeric variables, and allocate array used
  //to represent sets of variables
  totalVarNum = (predNum > 0) ? 2 * varNum * depth + 4 * predNum : 
    ((summary || image) ? 2 * varNum * (depth + 2) : 2 * varNum * depth);
  varSet = new int [totalVarNum];

  //display final options
  printf("depth = %d branch = %d repeat = %d disj = %d "
         "vars = %d unsat = %s qelim2 = %s\n",
         depth,branch,repeat,disj,varNum,
         unsat ? "true" : "false",qelim2 ? "true" : "false");
}

/*********************************************************************/
//create all kinds of managers
/*********************************************************************/
void CreateManagers()
{
  cudd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);
  if(tddType == DIA_DDD) theory = ddd_create_int_theory (totalVarNum);
  if(tddType == DIA_OCT) theory = oct_create_int_theory (totalVarNum);
  if(tddType == DIA_TVPI) theory = tvpi_create_int_theory (totalVarNum);
  tdd = tdd_init (cudd, theory);  
}

/*********************************************************************/
//create all kinds of managers
/*********************************************************************/
void DestroyManagers()
{
  tdd_quit(tdd);
  if(tddType == DIA_DDD) ddd_destroy_theory(theory);
  if(tddType == DIA_OCT) oct_destroy_theory(theory);
  if(tddType == DIA_TVPI) tvpi_destroy_theory(theory);
  Cudd_Quit(cudd);
}

#ifdef DEBUG
/*********************************************************************/
//utility function to print a DD. assumes that the DD has a single
//cube.
/*********************************************************************/
void PrintDD(tdd_node *node)
{
  Cudd_PrintMinterm (cudd, node);
  int *sup = Cudd_SupportIndex(cudd,node);
  //int ssize = Cudd_SupportSize(cudd,node);
  for(size_t i = 0;i < tdd->varsSize && tdd->ddVars[i] && Cudd_ReadVars(cudd,i);++i) {
    if(sup[i]) {
      if(Cudd_bddAnd(cudd,node,Cudd_bddIthVar(cudd,i)) != Cudd_ReadLogicZero(cudd)) {
        theory->print_lincons(stdout,tdd->ddVars[i]);
        printf(" && ");
      }
      if(Cudd_bddAnd(cudd,node,Cudd_Not(Cudd_bddIthVar(cudd,i))) != Cudd_ReadLogicZero(cudd)) {
        theory->print_lincons(stdout,theory->negate_cons(tdd->ddVars[i]));
        printf(" && ");
      }
    }
  }
  printf("\n");
  for(size_t i = 0;i < tdd->varsSize && tdd->ddVars[i] && Cudd_ReadVars(cudd,i);++i) {
    if(sup[i]) {
      printf("level of %d is %d\n",i,cuddI(cudd,i));
    }
  }
  printf("\n");
  free(sup);
}
#endif

/*********************************************************************/
//utility function for operating on tdd nodes. assumes that the
//argument is refed. derefs the arguments and refs the result. if op
//is "!", then the second argument should be NULL.
/*********************************************************************/
tdd_node *TddOp(tdd_node *arg1,tdd_node *arg2,char op)
{
  tdd_node *res = NULL;
  if(op == '&') {
    res = tdd_and(tdd,arg1,arg2);
  } else if(op == '|') {
    res = tdd_or(tdd,arg1,arg2);
  } else if(op == '^') {
    res = tdd_xor(tdd,arg1,arg2);
  } else if(op == '!') {
    res = tdd_not(arg1);
  } else {
    printf("ERROR: illegal operator %c passed to TddOp!\n",op);
    exit(1);
  }
  Cudd_Ref(res);  
  Cudd_RecursiveDeref(cudd,arg1);
  if(arg2) Cudd_RecursiveDeref(cudd,arg2);
  return res;
}

/*********************************************************************/
//create and return the tdd_node for the constraint C1 * X + C2 * Y <=
//K. refs the result.
/*********************************************************************/
tdd_node *ConsToTdd(int c1,int x,int c2,int y,int k)
{
#ifdef DEBUG
  printf("adding %d * x%d + %d * x%d <= %d\n",c1,x,c2,y,k);
#endif
  constant_t cst = theory->create_int_cst(k);
  memset(varSet,0,totalVarNum * sizeof(int));
  varSet[x] = c1;
  varSet[y] = c2;
  linterm_t term = theory->create_linterm(varSet,totalVarNum);
  lincons_t cons = theory->create_cons(term,0,cst);
  tdd_node *res = to_tdd(tdd,cons);
  theory->destroy_lincons(cons);
  Cudd_Ref(res);
  return res;
}

/*********************************************************************/
//quantify out all variables from min to max-1 from node and return
//the result. deref node.
/*********************************************************************/
tdd_node *Qelim(tdd_node *node,int min,int max)
{
  //clear variable set
  memset(varSet,0,totalVarNum * sizeof(int));

  //now quantify out elements if using qelim1, or set the elements of
  //varSet to 1 if using qelim2
  for(int i = min;i < max;++i) {
    if(qelim2) varSet[i] = 1;
    else {
#ifdef DEBUG
      printf("***** eliminating numeric variable %d ...\n",i);
#endif
      tdd_node *tmp = tdd_exist_abstract (tdd, node, i);
      Cudd_Ref (tmp);
      Cudd_RecursiveDeref (cudd, node);
      node = tmp;
#ifdef DEBUG
      printf ("node is:\n");
      PrintDD (node);
#endif
    }
  }

  //quantify, if using qelim2
  if(qelim2) {
    tdd_node *tmp = tdd_exist_abstract_v2 (tdd, node, varSet);
    Cudd_Ref (tmp);
    Cudd_RecursiveDeref (cudd, node);
    node = tmp;
  }

  //cleanup and return
  return node;
}

/*********************************************************************/
//create a tdd for X = Y
/*********************************************************************/
tdd_node *VarEq(int x,int y)
{
  tdd_node *node1 = ConsToTdd(1,x,-1,y,0);
  tdd_node *node2 = ConsToTdd(1,y,-1,x,0);
  return TddOp(node1,node2,'&');
}

/*********************************************************************/
//generate constants and coefficients for predicates, these are
//generated as an int array of size (5 * predNum) where each
//successive 5 elements are coeff1, var1, coeff2, var2, and the
//constant for a predicate.
/*********************************************************************/
int *Preds()
{
  if(predNum <= 0) return NULL;

  int *preds = new int [5 * predNum];

  for(int i = 0;i < predNum;++i) {
    if(consType == DIA_DDD) {
      preds[5 * i] = 1;
      preds[5 * i + 2] = -1;
    }
    if(consType == DIA_OCT) {
      preds[5 * i] = Rand(0,2) ? 1 : -1;
      preds[5 * i + 2] = Rand(0,2) ? 1 : -1;
    }
    if(consType == DIA_TVPI) {
      do { preds[5 * i] = Rand(-50,50); } while (preds[5 * i] == 0);
      do { preds[5 * i + 2] = Rand(-50,50); } while (preds[5 * i + 2] == 0);
    }
    preds[5 * i + 1] = Rand(0,2 * varNum);
    do {
      preds[5 * i + 3] = Rand(0,2 * varNum);
    } while (preds[5 * i + 3] == preds[5 * i + 1]);
    preds[5 * i + 4] = Rand(-1000,1000);
  }

  return preds;
}

/*********************************************************************/
//generate constant bounds for transition relation invariants. there
//are as many bounds as the number of disjuncts in the invariant. the
//invariant at the join points after each diamond is ||( X - Y <= K_i)
/*********************************************************************/
int **Bounds()
{
  int **bounds = new int* [varNum];

  for(size_t i = 0;i < varNum;++i) {
    bounds[i] = new int [disj];
    for(size_t j = 0;j < disj;++j) bounds[i][j] = Rand(-1000,1000);
  }

  return bounds;
}

/*********************************************************************/
//generate coefficients for the transition relation constraints
/*********************************************************************/
int *Coeffs()
{
  int *coeffs = new int [2 * varNum];

  for(size_t i = 0;i < varNum;++i) {
    if(consType == DIA_DDD) {
      coeffs[2 * i] = 1;
      coeffs[2 * i + 1] = -1;
    }
    if(consType == DIA_OCT) {
      coeffs[2 * i] = Rand(0,2) ? 1 : -1;
      coeffs[2 * i + 1] = Rand(0,2) ? 1 : -1;
    }
    if(consType == DIA_TVPI) {
      do { coeffs[2 * i] = Rand(-50,50); } while (coeffs[2 * i] == 0);
      do { coeffs[2 * i + 1] = Rand(-50,50); } while (coeffs[2 * i + 1] == 0);
    }
  }

  return coeffs;
}

/*********************************************************************/
//generate constraints that relate initial state variables or
//predicates to initial transition relation variables
/*********************************************************************/
tdd_node *InitCons(int *preds)
{
#ifdef DEBUG
  printf("generating INIT constraints ...\n");
#endif

  //the largest transition relation variable (+1)
  int maxTransVar = 2 * varNum * depth;

  //the result to be computed
  tdd_node *node = tdd_get_true(tdd);
  Cudd_Ref(node);
  
  //if we are using predicate abstraction -- this implies summary or
  //image computation
  if(preds) {
    //generate predicate constraints
    for(int i = 0;i < predNum;++i) {
      int id = 5 * i;
      tdd_node *pred1 = ConsToTdd(preds[id],preds[id + 1],preds[id + 2],
                                  preds[id + 3],preds[id + 4]);
      
      int v1 = maxTransVar + 2 * i;
      int v2 = v1 + 1;
      tdd_node *pred2 = ConsToTdd(1,v1,-1,v2,0);
      tdd_node *eq = TddOp(TddOp(pred1,pred2,'^'),NULL,'!');
      node = TddOp(node,eq,'&');
    }
  }
  
#ifdef DEBUG
  printf ("INIT node is:\n");
  PrintDD(node);
#endif

  //all done
  return node;
}

/*********************************************************************/
//generate constraints that make the transition relation UNSAT
/*********************************************************************/
tdd_node *Unsat(int **bounds,int *coeffs,int d)
{
#ifdef DEBUG
  printf("generating UNSAT constraints ...\n");
#endif

  tdd_node *choice = tdd_get_false(tdd);
  Cudd_Ref(choice);
  for(size_t vn1 = 0;vn1 < varNum;++vn1) {
    int v1 = 2 * (varNum * d + vn1);
    int v2 = v1 + 1;
    tdd_node *unsat = tdd_get_true(tdd);
    Cudd_Ref(unsat);
    for(size_t vn2 = 0;vn2 < varNum;++vn2) {
      for(size_t i = 0;i < disj;++i) {
        tdd_node *node1 = ConsToTdd(-coeffs[2 * vn2 + 1],v2,-coeffs[2 * vn2],v1,-bounds[vn2][i]-1);
        unsat = TddOp(unsat,node1,'&');
      }
    }
    choice = TddOp(choice,unsat,'|');
  }

#ifdef DEBUG
  printf ("UNSAT node is:\n");
  PrintDD(choice);
#endif

  return choice;
}

/*********************************************************************/
//generate constraints that enforce the invariant at the start of the
//transition relation
/*********************************************************************/
tdd_node *InitInv(int **bounds,int *coeffs,int d)
{
  tdd_node *node = tdd_get_true(tdd);
  Cudd_Ref(node);

  for(size_t vn = 0;vn < varNum;++vn) {
    int v1 = 2 * (varNum * d + vn);
    int v2 = v1 + 1;

    //generate the top-level disjunctive invariant 
    tdd_node *choice = tdd_get_false(tdd);
    Cudd_Ref(choice);

    for(size_t i = 0;i < disj;++i) {
      //create constraint v1 - v2 <= bound
      tdd_node *node1 = ConsToTdd(coeffs[v1],v1,coeffs[v2],v2,bounds[vn][i]);
      choice = TddOp(choice,node1,'|');
    }

    node = TddOp(node,choice,'&');
  }
#ifdef DEBUG
  printf ("INIT Invariant node is:\n");
  PrintDD(node);
#endif

  return node;
}

/*********************************************************************/
//unwind the transition relation by relating variables at step d to
//those at step d-1 such that the invariant is maintained
/*********************************************************************/
tdd_node *Unwind(int d)
{
  tdd_node *node = tdd_get_true(tdd);
  Cudd_Ref(node);

  for(size_t vn = 0;vn < varNum;++vn) {
    int v1 = 2 * (varNum * d + vn);
    int v2 = v1 + 1;

    //get the branching factor
    int bfac = Rand(1,branch + 1);
#ifdef DEBUG
    printf("level = %d\tbranching = %d\n",d,bfac);
#endif

    //get the previous variables to relate to v1 and v2
    int pv1 = compInv ? 
      (2 * (varNum * (d - 1) + Rand(0,varNum))) : (v1 - 2 * varNum);
    int pv2 = pv1 + 1;

    //disjunctive choices at the start of this diamond
    tdd_node *choice = tdd_get_false(tdd);
    Cudd_Ref(choice);

    //for DDD constraints
    if(consType == DIA_DDD) {
      //create branches
      for(int i = 0;i < bfac;++i) {
        //create a random positive slippage
        int slip = Rand(0,1000);

        //create two constraints v1 <= pv1 - slip and v2 >= pv2 +
        //slip. together with the previous invariant pv1 - pv2 <= bound,
        //this ensures the new invariant v1 - v2 <= bound.
        tdd_node *node1 = ConsToTdd(1,v1,-1,pv1,-slip);
        tdd_node *node2 = ConsToTdd(1,pv2,-1,v2,-slip);
        choice = TddOp(choice,TddOp(node1,node2,'&'),'|');
      }
    }
    //for non-DDD constraints
    else {
      //create constraints v1 = pv1 and v2 = pv2. together with
      //the previous invariant c1*pv1 + c2*pv2 <= bound, this
      //ensures the new invariant c1*v1 + c2*v2 <= bound.
      tdd_node *node1 = VarEq(v1,pv1);
      tdd_node *node2 = VarEq(v2,pv2);
      choice = TddOp(choice,TddOp(node1,node2,'&'),'|');
    }

#ifdef DEBUG
    printf ("choice is:\n");
    PrintDD(choice);
#endif

    //add the choice
    node = TddOp(node,choice,'&');
  }

#ifdef DEBUG
  printf ("node is:\n");
  PrintDD(node);
#endif

  return node;
}

/*********************************************************************/
//generate constraints that relate final state variables or predicates
//to final transition relation variables
/*********************************************************************/
tdd_node *FinalCons(int *preds)
{
#ifdef DEBUG
  printf("generating FINAL constraints ...\n");
#endif

  //the largest transition relation variable (+1)
  int maxTransVar = 2 * varNum * depth;

  //the result to be computed
  tdd_node *node = tdd_get_true(tdd);
  Cudd_Ref(node);

  //if we are using predicate abstraction -- this implies summary or
  //image computation
  if(preds) {
    //generate predicate constraints
    for(int i = 0;i < predNum;++i) {
      int id = 5 * i;
      int baseVar = 2 * varNum * (depth - 1);
      tdd_node *pred1 = ConsToTdd(preds[id],baseVar + preds[id + 1],
                                  preds[id + 2],baseVar + preds[id + 3],
                                  preds[id + 4]);      
      int v1 = maxTransVar + 2 * (predNum + i);
      int v2 = v1 + 1;
      tdd_node *pred2 = ConsToTdd(1,v1,-1,v2,0);
      tdd_node *eq = TddOp(TddOp(pred1,pred2,'^'),NULL,'!');
      node = TddOp(node,eq,'&');
    }
  }
  
#ifdef DEBUG
  printf ("FINAL node is:\n");
  PrintDD(node);
#endif

  //all done
  return node;
}

/*********************************************************************/
//check final result
/*********************************************************************/
void CheckResult(tdd_node *node)
{
  if(unsat) {
    //condition under which we should expect true after QELIM
    bool expTrue = !summary && !image;
    if(!expTrue || node == Cudd_ReadLogicZero (cudd))
      printf("GOOD: result is UNSAT as expected!\n");
    else {
      printf("ERROR: result is SAT, UNSAT expected!\n");
      exit(1);
    }
  } else {
    //condition under which we should expect true after QELIM
    bool expTrue = !summary && !image;
    if((!expTrue && node != Cudd_ReadLogicZero (cudd)) || (expTrue && node == Cudd_ReadOne (cudd)))
      printf("GOOD: result is SAT as expected!\n");
    else {
      printf("ERROR: result is UNSAT, SAT expected!\n");
      exit(1);
    }
  }
}

/*********************************************************************/
//generate constraints and then quantify out all transition relation
//variables. each step of the transition relation introduces 2 *
//varNum fresh variables. therefore, total number of variables in the
//transition relation is K = 2 * varNum * depth. these are numbered
//from 0 to K-1. in general, the variables at step I (first step being
//step 0) are numbered from 2 * varNum * I to 2 * varNum * (I+1) -
//1. if predicate abstraction is used (with P predicates), then we use
//2 * P * 2 additional variables for predicates. these are numbered
//from 2 * varNum * depth to 2 * varNum * depth + 2 * P * 2 - 1. if
//predicate abstraction is not used, then we use 2 * varNum * 2
//additional variables for initial and final numeric variables. these
//are numbered from 2 * varNum * depth to 2 * varNum * (depth + 2) -
//1.
/*********************************************************************/
void GenAndSolve()
{
  //the minimum and maximum variables for the transition relation
  int minTransVar = 0;
  int maxTransVar = 2 * varNum * depth;

  //generate constants and coefficients for predicates
  int *preds = Preds();

  //generate bounds and coefficients for transition relation invariant
  int **bounds = Bounds();
  int *coeffs = Coeffs();

  //the depth at which we are going to generate the UNSAT clause
  int target = Rand(0,depth);

#ifdef DEBUG
  printf("target = %d\n",target);
#endif

  //the overall tdd
  tdd_node *node = tdd_get_true(tdd);
  Cudd_Ref(node);

  //create transition relation
  for(int d = 0;d < depth;++d) {
    //generate a constraint that makes the whole system unsatisfiable,
    //if needed
    if(unsat && d == target) 
      node = TddOp(node,Unsat(bounds,coeffs,d),'&');

    //if at the start of the program
    if(d == 0) {
      node = TddOp(node,InitInv(bounds,coeffs,d),'&');      
      continue;
    }

    //not at the start of the program -- generate constraints that
    //preserve the invariant by relating fresh variables with the
    //variables from the previous step
    node = TddOp(node,Unwind(d),'&');      
  }

  //if not computing image or summary
  if(!summary && !image) node = Qelim(node,minTransVar,maxTransVar);

  //if doing predicate abstraction
  else if(preds) {
    //generate initial and final constraints
    node = TddOp(node,InitCons(preds),'&');
    node = TddOp(node,FinalCons(preds),'&');
    
    //compute image or summary
    if(summary) node = Qelim(node,minTransVar,maxTransVar);
    else node = Qelim(node,minTransVar,maxTransVar + 2 * predNum);
  }

  //if computing summary without predicate abstraction
  else if(summary) {
    node = Qelim(node,minTransVar + 2 * varNum,maxTransVar - 2 * varNum);
  }

  //if computing image without predicate abstraction
  else {
    node = Qelim(node,minTransVar,maxTransVar - 2 * varNum);
  }

  //check if the result is correct
  CheckResult(node);

  //cleanup
  Cudd_RecursiveDeref(cudd,node);
  for(size_t i = 0;i < varNum;++i) delete [] bounds[i];
  if(preds) delete [] preds;
  delete [] bounds;
  delete [] coeffs;
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
  delete [] varSet;
  return 0;
}

/*********************************************************************/
//end of diamond.cpp
/*********************************************************************/

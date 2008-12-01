#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cassert>
#include <ctime>
#include <string>
#include <set>
using namespace std;

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
#include "smt_formula.h"

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
int randSeed = -1;
string smtOut;
FILE *smtFile = NULL;
bool unsat = false;
bool qelim2 = false;
bool compInv = false;
enum TddType { DIA_DDD, DIA_OCT, DIA_TVPI } 
  tddType = DIA_DDD,consType = DIA_DDD;
bool summary = false;
bool image = false;
bool eagerElim = false;

//other data structures
int totalVarNum = 0;
int *varSet = NULL;
DdManager *cudd = NULL;
tdd_manager *tdd = NULL;
theory_t *theory = NULL;

//we will use a pair of tdd_node and a smt_formula to compute our
//result. if we are solving we will use the tdd_node part. otherwise,
//if we are generating a SMT formula, we will use the smt_formula
//part.
class Formula
{
public:
  tdd_node *node;
  smt_formula_t *smtf;

  Formula() { node = NULL; smtf = NULL; }
};

/*********************************************************************/
//return a random integer between min (inclusive) and max (exclusive)
/*********************************************************************/
int Rand(int min,int max)
{
  if(min >= max) {
    printf("ERROR: can't generate a random number between %d and %d!!\n",min,max);
    exit(1);
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
  printf("\t--srand <K> : use randon seed K\n");
  printf("\t--smtOut <K> : output SMT formula to file K\n");
  printf("\t--unsat : generate unsatisfiable constraints\n");
  printf("\t--qelim2 : use QELIM algorithm that relies on a theory solver\n");
  printf("\t--oct : use octagon theory\n");
  printf("\t--octCons : use octagon constraints\n");
  printf("\t--tvpi : use TVPI theory\n");
  printf("\t--tvpiCons : use TVPI constraints\n");
  printf("\t--compInv : enable propositionally complex invariants\n");
  printf("\t--summary : whether to compute summaries\n");
  printf("\t--image : whether to do image computation\n");
  printf("\t--eagerElim : whether to do eager quantifier elimination\n");
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
    else if(!strcmp(argv[i],"--srand") && i < argc-1) {
      randSeed = atoi(argv[++i]);
    }
    else if(!strcmp(argv[i],"--smtOut") && i < argc-1) {
      smtOut = argv[++i];
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
    else if(!strcmp(argv[i],"--eagerElim")) eagerElim = true;
    else {
      Usage(argv[0]);
      exit(1);
    }
  }

  //sanity check on various option values
  if(depth <= 0) {
    printf("ERROR: depth must be greater than zero!\n");
    exit(1);
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

/*********************************************************************/
//create the preamble for the SMT file
/*********************************************************************/
void CreateSMTPreamble(int argc,char *argv[],char *fileName)
{
  fprintf(smtFile,"(benchmark %s\n",fileName);
  fprintf(smtFile,":source {\n");
  for(int i = 0;i < argc;++i) {
    fprintf(smtFile," %s",argv[i]);
  }
  fprintf(smtFile,"\n}\n:status %s\n",unsat ? "unsat" : "sat");
  fprintf(smtFile,":category { crafted }\n:difficulty { 0 }\n");
  fprintf(smtFile,":logic AUFLIA\n");
}

#ifdef DEBUG
/*********************************************************************/
//utility function to print a DD. assumes that the DD has a single
//cube.
/*********************************************************************/
void PrintDD(Formula form)
{
  if(smtFile) {
    smt_print_formula(stdout,form.smtf);
    printf("\n");
  } else {
    tdd_node *node = form.node;
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
}
#endif

/*********************************************************************/
//get TRUE or FALSE formula. the argument indicates if the result is
//TRUE. if we are generating SMT, then we return a NULL formula,
//assuming that it will only be used as an identity later on.
/*********************************************************************/
Formula ConstFormula(bool isTrue)
{
  Formula res;
  if(!smtFile) {
    res.node = isTrue ? tdd_get_true(tdd) : tdd_get_false(tdd);
    Cudd_Ref(res.node);
  }
  return res;
}

/*********************************************************************/
//utility function for operating on tdd nodes. assumes that the
//argument is refed. derefs the arguments and refs the result. if op
//is "!", then the second argument should be NULL.
/*********************************************************************/
Formula FormOp(Formula arg1,Formula arg2,char op)
{
  Formula res;
  //if generating SMT file
  if(smtFile) {
    if(op == '&' || op == '|') {
      //if arg1 is identity
      if(!arg1.smtf) return arg2;
      //if arg2 is identity
      if(!arg2.smtf) return arg1;
      //create AND or OR formula
      res.smtf = (smt_formula_t*)malloc(sizeof(smt_formula_t));
      memset(res.smtf,0,sizeof(smt_formula_t));
      res.smtf->type = (op == '&') ? SMT_AND : SMT_OR;
      res.smtf->subs = (smt_formula_t**)malloc(3 * sizeof(smt_formula_t*));
      res.smtf->subs[0] = arg1.smtf;
      res.smtf->subs[1] = arg2.smtf;
      res.smtf->subs[2] = NULL;
    } else if(op == '!') {
      res.smtf = (smt_formula_t*)malloc(sizeof(smt_formula_t));
      memset(res.smtf,0,sizeof(smt_formula_t));
      res.smtf->type = SMT_NOT;
      res.smtf->subs = (smt_formula_t**)malloc(2 * sizeof(smt_formula_t*));
      res.smtf->subs[0] = arg1.smtf;
      res.smtf->subs[1] = NULL;
    } else {
      printf("ERROR: illegal operator %c passed to FormOp!\n",op);
      exit(1);
    }    
  }
  //if solving formula
  else {
    if(op == '&') {
      res.node = tdd_and(tdd,arg1.node,arg2.node);
    } else if(op == '|') {
      res.node = tdd_or(tdd,arg1.node,arg2.node);
    } else if(op == '!') {
      res.node = tdd_not(arg1.node);
    } else {
      printf("ERROR: illegal operator %c passed to FormOp!\n",op);
      exit(1);
    }
    Cudd_Ref(res.node);  
    Cudd_RecursiveDeref(cudd,arg1.node);
    if(arg2.node) Cudd_RecursiveDeref(cudd,arg2.node);
  }
  return res;
}

/*********************************************************************/
//create and return the tdd_node for the constraint C1 * X + C2 * Y <=
//K. refs the result.
/*********************************************************************/
Formula ConsToTdd(int c1,int x,int c2,int y,int k)
{
#ifdef DEBUG
  printf("adding %d * x%d + %d * x%d <= %d\n",c1,x,c2,y,k);
#endif
  Formula res;
  //if creating SMT file
  if(smtFile) {
    char v1[28],v2[28];
    snprintf(v1,28,"x%d",x);
    snprintf(v2,28,"x%d",y);
    res.smtf = smt_create_cons(c1,v1,c2,v2,0,k);
  }
  //if solving
  else {
    constant_t cst = theory->create_int_cst(k);
    memset(varSet,0,totalVarNum * sizeof(int));
    varSet[x] = c1;
    varSet[y] = c2;
    linterm_t term = theory->create_linterm(varSet,totalVarNum);
    lincons_t cons = theory->create_cons(term,0,cst);
    res.node = to_tdd(tdd,cons);
    theory->destroy_lincons(cons);
    Cudd_Ref(res.node);
  }
  return res;
}

/*********************************************************************/
//quantify out all variables from min to max-1 from node and return
//the result. deref node.
/*********************************************************************/
Formula Qelim(Formula form,int min,int max)
{
  //if generating SMT file
  if(smtFile) {
    //create EXISTS formula
    smt_formula_t *res = (smt_formula_t*)malloc(sizeof(smt_formula_t));
    memset(res,0,sizeof(smt_formula_t));
    res->type = SMT_EXISTS;
    res->subs = (smt_formula_t**)malloc(2 * sizeof(smt_formula_t*));
    res->subs[0] = form.smtf;
    res->subs[1] = NULL;
    res->qVars = (char**)malloc((max - min + 1) * sizeof(char*));
    int i = 0;
    char var[28];
    for(;i < max - min;++i) {
      snprintf(var,28,"x%d",min + i);
      res->qVars[i] = strdup(var);
    }
    res->qVars[max - min] = NULL;
    //rename each quantified variable "x" to "?x". this seems to be
    //the SMT convention.
    for(i = 0;i < max - min;++i) {
      snprintf(var,28,"x%d",min + i);
      string old = var;
      string sub = "?" + old;
      smt_rename_var(res,(char*)old.c_str(),(char*)sub.c_str());
    }
    //all done
    form.smtf = res;
  }
  else {
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
        tdd_node *tmp = tdd_exist_abstract (tdd, form.node, i);
        Cudd_Ref (tmp);
        Cudd_RecursiveDeref (cudd, form.node);
        form.node = tmp;
#ifdef DEBUG
        printf ("node is:\n");
        PrintDD (form);
#endif
      }
    }

    //quantify, if using qelim2
    if(qelim2) {
      tdd_node *tmp = tdd_exist_abstract_v2 (tdd, form.node, varSet);
      Cudd_Ref (tmp);
      Cudd_RecursiveDeref (cudd, form.node);
      form.node = tmp;
    }
  }

  //all done
  return form;
}

/*********************************************************************/
//create a tdd for X = Y
/*********************************************************************/
Formula VarEq(int x,int y)
{
  Formula form1 = ConsToTdd(1,x,-1,y,0);
  Formula form2 = ConsToTdd(1,y,-1,x,0);
  return FormOp(form1,form2,'&');
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
Formula InitCons(int *preds)
{
#ifdef DEBUG
  printf("generating INIT constraints ...\n");
#endif

  //the largest transition relation variable (+1)
  int maxTransVar = 2 * varNum * depth;

  //the result to be computed
  Formula form = ConstFormula(true);
  
  //if we are using predicate abstraction -- this implies summary or
  //image computation
  if(preds) {
    //generate predicate constraints
    for(int i = 0;i < predNum;++i) {
      int id = 5 * i;
      Formula pred11 = ConsToTdd(preds[id],preds[id + 1],preds[id + 2],
                                 preds[id + 3],preds[id + 4]);
      Formula pred12 = ConsToTdd(preds[id],preds[id + 1],preds[id + 2],
                                 preds[id + 3],preds[id + 4]);
      pred12 = FormOp(pred12,Formula(),'!');
      
      int v1 = maxTransVar + 2 * i;
      int v2 = v1 + 1;
      Formula pred21 = ConsToTdd(1,v1,-1,v2,0);
      Formula pred22 = ConsToTdd(1,v1,-1,v2,0);
      pred22 = FormOp(pred22,Formula(),'!');

      Formula eq = FormOp(FormOp(pred11,pred21,'&'),FormOp(pred12,pred22,'&'),'|');
      form = FormOp(form,eq,'&');
    }
  }
  
#ifdef DEBUG
  printf ("INIT node is:\n");
  PrintDD(form);
#endif

  //all done
  return form;
}

/*********************************************************************/
//generate constraints that make the transition relation UNSAT
/*********************************************************************/
Formula Unsat(int **bounds,int *coeffs,int d)
{
#ifdef DEBUG
  printf("generating UNSAT constraints ...\n");
#endif

  Formula choice = ConstFormula(false);

  for(size_t vn1 = 0;vn1 < varNum;++vn1) {
    int v1 = 2 * (varNum * d + vn1);
    int v2 = v1 + 1;

    Formula unsat = ConstFormula(true);

    for(size_t vn2 = 0;vn2 < varNum;++vn2) {
      for(size_t i = 0;i < disj;++i) {
        Formula node1 = ConsToTdd(-coeffs[2 * vn2 + 1],v2,-coeffs[2 * vn2],v1,-bounds[vn2][i]-1);
        unsat = FormOp(unsat,node1,'&');
      }
    }

    choice = FormOp(choice,unsat,'|');

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
Formula InitInv(int **bounds,int *coeffs,int d)
{
  Formula node = ConstFormula(true);

  for(size_t vn = 0;vn < varNum;++vn) {
    int v1 = 2 * (varNum * d + vn);
    int v2 = v1 + 1;

    //generate the top-level disjunctive invariant 
    Formula choice = ConstFormula(false);

    for(size_t i = 0;i < disj;++i) {
      //create constraint v1 - v2 <= bound
      Formula node1 = ConsToTdd(coeffs[v1],v1,coeffs[v2],v2,bounds[vn][i]);
      choice = FormOp(choice,node1,'|');
    }

    node = FormOp(node,choice,'&');
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
Formula Unwind(int d)
{
  Formula node = ConstFormula(true);

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
    Formula choice = ConstFormula(false);

    //for DDD constraints
    if(consType == DIA_DDD) {
      //create branches
      for(int i = 0;i < bfac;++i) {
        //create a random positive slippage
        int slip = Rand(0,1000);

        //create two constraints v1 <= pv1 - slip and v2 >= pv2 +
        //slip. together with the previous invariant pv1 - pv2 <= bound,
        //this ensures the new invariant v1 - v2 <= bound.
        Formula node1 = ConsToTdd(1,v1,-1,pv1,-slip);
        Formula node2 = ConsToTdd(1,pv2,-1,v2,-slip);
        choice = FormOp(choice,FormOp(node1,node2,'&'),'|');
      }
    }
    //for non-DDD constraints
    else {
      //create constraints v1 = pv1 and v2 = pv2. together with
      //the previous invariant c1*pv1 + c2*pv2 <= bound, this
      //ensures the new invariant c1*v1 + c2*v2 <= bound.
      Formula node1 = VarEq(v1,pv1);
      Formula node2 = VarEq(v2,pv2);
      choice = FormOp(choice,FormOp(node1,node2,'&'),'|');
    }

#ifdef DEBUG
    printf ("choice is:\n");
    PrintDD(choice);
#endif

    //add the choice
    node = FormOp(node,choice,'&');
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
Formula FinalCons(int *preds)
{
#ifdef DEBUG
  printf("generating FINAL constraints ...\n");
#endif

  //the largest transition relation variable (+1)
  int maxTransVar = 2 * varNum * depth;

  //the result to be computed
  Formula node = ConstFormula(true);

  //if we are using predicate abstraction -- this implies summary or
  //image computation
  if(preds) {
    //generate predicate constraints
    for(int i = 0;i < predNum;++i) {
      int id = 5 * i;
      int baseVar = 2 * varNum * (depth - 1);
      Formula pred11 = ConsToTdd(preds[id],baseVar + preds[id + 1],
                                 preds[id + 2],baseVar + preds[id + 3],
                                 preds[id + 4]);      
      Formula pred12 = ConsToTdd(preds[id],baseVar + preds[id + 1],
                                 preds[id + 2],baseVar + preds[id + 3],
                                 preds[id + 4]);      
      pred12 = FormOp(pred12,Formula(),'!');

      int v1 = maxTransVar + 2 * (predNum + i);
      int v2 = v1 + 1;

      Formula pred21 = ConsToTdd(1,v1,-1,v2,0);
      Formula pred22 = ConsToTdd(1,v1,-1,v2,0);
      pred22 = FormOp(pred22,Formula(),'!');

      Formula eq = FormOp(FormOp(pred11,pred21,'&'),FormOp(pred12,pred22,'&'),'|');
      node = FormOp(node,eq,'&');
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
//declare free variables
/*********************************************************************/
void DeclFreeVars(smt_formula_t *f,set<string> &fv)
{
  int i = 0;
  switch(f->type) {
  case SMT_CONS:
    for(;i < 2;++i) {
      if(f->cons->vars[i][0] != '?') {
        if(fv.insert(f->cons->vars[i]).second) {
          fprintf(smtFile,":extrafuns ((%s Int))\n",f->cons->vars[i]);
        }
      }
    }
    break;
  case SMT_AND:
  case SMT_OR:
  case SMT_NOT:
    while(f->subs[i]) DeclFreeVars(f->subs[i++],fv);
    break;
  case SMT_EXISTS:
  case SMT_FORALL:    
    DeclFreeVars(f->subs[0],fv);
    break;
  default:
    printf("ERROR: illegal SMT formula type %d!\n",f->type);
    exit(1);
  }
}

/*********************************************************************/
//print SMT formula
/*********************************************************************/
void PrintSmt(smt_formula_t *smtf)
{
  //declare free variables
  set<string> fv;
  DeclFreeVars(smtf,fv);
  //print the formula
  fprintf(smtFile,":formula\n");
  smt_print_formula(smtFile,smtf);
  fprintf(smtFile,")\n");
}

/*********************************************************************/
//do final quantifier elimination
/*********************************************************************/
Formula FinalQelim(Formula form)
{
  //the minimum and maximum variables for the transition relation
  int minTransVar = 0;
  int maxTransVar = 2 * varNum * depth;

  //generate constants and coefficients for predicates
  int *preds = Preds();

  //if not computing image or summary
  if(!summary && !image) form = Qelim(form,minTransVar,maxTransVar);

  //if doing predicate abstraction
  else if(preds) {
    //generate initial and final constraints
    form = FormOp(form,InitCons(preds),'&');
    form = FormOp(form,FinalCons(preds),'&');
    
    //compute image or summary
    if(summary) form = Qelim(form,minTransVar,maxTransVar);
    else form = Qelim(form,minTransVar,maxTransVar + 2 * predNum);
  }

  //if computing summary without predicate abstraction
  else if(summary) {
    form = Qelim(form,minTransVar + 2 * varNum,maxTransVar - 2 * varNum);
  }

  //if computing image without predicate abstraction
  else {
    form = Qelim(form,minTransVar,maxTransVar - 2 * varNum);
  }

  //cleanup and return
  if(preds) delete [] preds;
  return form;
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
  //generate bounds and coefficients for transition relation invariant
  int **bounds = Bounds();
  int *coeffs = Coeffs();

  //the depth at which we are going to generate the UNSAT clause
  int target = Rand(0,depth);

#ifdef DEBUG
  printf("target = %d\n",target);
#endif

  //the overall tdd
  Formula form = ConstFormula(true);

  //create transition relation
  for(int d = 0;d < depth;++d) {
    //generate a constraint that makes the whole system unsatisfiable,
    //if needed
    if(unsat && d == target) 
      form = FormOp(form,Unsat(bounds,coeffs,d),'&');

    //if at the start of the program
    if(d == 0) {
      form = FormOp(form,InitInv(bounds,coeffs,d),'&');      
      continue;
    }

    //not at the start of the program -- generate constraints that
    //preserve the invariant by relating fresh variables with the
    //variables from the previous step
    form = FormOp(form,Unwind(d),'&');      
  }

  //do final quantifier elimination
  form = FinalQelim(form);

  //print SMT formula or check if the result is correct
  if(smtFile) PrintSmt(form.smtf);
  else CheckResult(form.node);

  //cleanup
  if(smtFile) smt_destroy_formula(form.smtf);
  else Cudd_RecursiveDeref(cudd,form.node);
  for(size_t i = 0;i < varNum;++i) delete [] bounds[i];
  delete [] bounds;
  delete [] coeffs;
}

/*********************************************************************/
//the main procedure
/*********************************************************************/
int main(int argc,char *argv[])
{
  ProcessInputs(argc,argv);
  srand(randSeed < 0 ? time(NULL) : randSeed);
  for(size_t i = 0;i < repeat;++i) {
    //open SMT file
    if(!smtOut.empty()) {
      char fileName[256];
      snprintf(fileName,256,"%s.%d.smt",smtOut.c_str(),i);
      smtFile = fopen(fileName,"w");
      if(smtFile == NULL) {
        printf("ERROR: cannot open SMT file %s!\n",fileName);
        exit(1);        
      }
      //create SMT file preamble
      CreateSMTPreamble(argc,argv,fileName);      
    }

    CreateManagers();
    GenAndSolve();
    DestroyManagers();

    //close SMT file
    if(!smtOut.empty()) {
      fclose(smtFile);
    }
  }
  delete [] varSet;
  return 0;
}

/*********************************************************************/
//end of diamond.cpp
/*********************************************************************/

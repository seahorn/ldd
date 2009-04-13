#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <limits.h>
#include <string>
#include <list>
#include <set>
using namespace std;

#include "tdd.h"
#include "tdd-ddd.h"
#include "tdd-oct.h"
#include "tdd-tvpi.h"
#include "smt_formula.h"

/**********************************************************************
 * need these things from the SMT parser
 *********************************************************************/
extern "C" {
  extern int yyparse(void);
  extern smt_formula_t *smtFormula;
  extern FILE *yyin;
}

/*********************************************************************/
//global variables -- store command line options
/*********************************************************************/
list<string> fileNames;
bool noqelim = false;
bool qelim2 = false;
bool qelim_occur = false;
bool qelim_approx = false;
bool verbose = false;
enum TddType { QSLV_DDD, QSLV_OCT, QSLV_TVPI } 
  tddType = QSLV_DDD,consType = QSLV_DDD;

/*********************************************************************/
//other data structures
/*********************************************************************/
int totalVarNum = 0;
int *varSet = NULL;
DdManager *cudd = NULL;
tdd_manager *tdd = NULL;
theory_t *theory = NULL;

/*********************************************************************/
//display usage
/*********************************************************************/
void Usage(char *cmd)
{
  printf("Usage : %s <option|filename> <option|filename> ...\n",cmd);
  printf("Options:\n");
  printf("\t--help|-h : display usage and exit\n");
  printf("\t--qelim2 : use QELIM algorithm that relies on a theory solver\n");
  printf("\t--oct : use octagon theory\n");
  printf("\t--tvpi : use TVPI theory\n");
  printf("\t--qelim-occur: use Least Occurrences First Quantified heuristic\n");
  printf("\t--noqelim: do not do quantifier elimination\n");
  printf("\t--qelim-approx: Approximate using BDD quantification\n");
  printf("\t--verbose: be verbose\n");
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
    }
    else if(!strcmp(argv[i],"--qelim2")) qelim2 = true;
    else if(!strcmp(argv[i],"--verbose")) verbose = true;
    else if(!strcmp(argv[i],"--qelim-occur")) 
      {qelim2 = false; qelim_occur=true; }
    else if(!strcmp(argv[i],"--qelim-approx")) 
      { qelim2 = true; qelim_approx=true; }
    else if(!strcmp(argv[i],"--noqelim")) noqelim=true;
    else if(!strcmp(argv[i],"--oct")) tddType = QSLV_OCT;
    else if(!strcmp(argv[i],"--tvpi")) tddType = QSLV_TVPI;
    else if(strstr(argv[i],".smt") == (argv[i] + strlen(argv[i]) - 4)) fileNames.push_back(argv[i]);
    else {
      Usage(argv[0]);
      exit(1);
    }
  }
}

/*********************************************************************/
//create all kinds of managers
/*********************************************************************/
void CreateManagers()
{
  cudd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);
  if(tddType == QSLV_DDD) theory = ddd_create_int_theory (totalVarNum);
  if(tddType == QSLV_OCT) theory = oct_create_int_theory (totalVarNum);
  if(tddType == QSLV_TVPI) theory = tvpi_create_int_theory (totalVarNum);
  tdd = tdd_init (cudd, theory);  
}

/*********************************************************************/
//create all kinds of managers
/*********************************************************************/
void DestroyManagers()
{
  tdd_quit(tdd);
  if(tddType == QSLV_DDD) ddd_destroy_theory(theory);
  if(tddType == QSLV_OCT) oct_destroy_theory(theory);
  if(tddType == QSLV_TVPI) tvpi_destroy_theory(theory);
  Cudd_Quit(cudd);
}

/*********************************************************************/
//get TRUE or FALSE formula. the argument indicates if the result is
//TRUE. if we are generating SMT, then we return a NULL formula,
//assuming that it will only be used as an identity later on.
/*********************************************************************/
tdd_node *ConstFormula(bool isTrue)
{
  tdd_node *res = isTrue ? tdd_get_true(tdd) : tdd_get_false(tdd);
  Cudd_Ref(res);
  return res;
}

/*********************************************************************/
//utility function for operating on tdd nodes. assumes that the
//argument is refed. derefs the arguments and refs the result. if op
//is "!", then the second argument should be NULL.
/*********************************************************************/
tdd_node * FormOp(tdd_node * arg1,tdd_node * arg2,char op)
{
  tdd_node * res;
  if(op == '&') {
    res = tdd_and(tdd,arg1,arg2);
  } else if(op == '|') {
    res = tdd_or(tdd,arg1,arg2);
  } else if(op == '!') {
    res = tdd_not(arg1);
  } else {
    printf("ERROR: illegal operator %c passed to FormOp!\n",op);
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
tdd_node * ConsToTdd(int c1,int x,int c2,int y,int k)
{
  // -- allow trivial constraints where x and y are the same
  if (x == y)
    if (c1 + c2 == 0)
      return 0 <= k ? ConstFormula (true) : ConstFormula (false);
    else
      {
	fprintf (stderr, "Constraint %d * x%d + %d * x%d <= %d\n",
		 c1, x, c2, y, k);
	assert (false);
      }
  
  

  
  if (tddType == QSLV_DDD)
    assert (c1 == -1 || c2 == -1);

  tdd_node * res;
  constant_t cst = theory->create_int_cst(k);
  memset(varSet,0,totalVarNum * sizeof(int));
  varSet[x] = c1;
  varSet[y] = c2;
  linterm_t term = theory->create_linterm(varSet,totalVarNum);
  lincons_t cons = theory->create_cons(term,0,cst);
  res = to_tdd(tdd,cons);
  theory->destroy_lincons(cons);
  Cudd_Ref(res);
  return res;
}

/*********************************************************************/
//convert a variable name to an index, starting with 0. currently, we
//assume that variables are of the form "xN" or "?xN" and the
//corresponding index is "N".
/*********************************************************************/
int VarId(char *var)
{
  if(var[0] == '?') return atoi(var + 2);
  else return atoi(var + 1);
}

int* occurrences;
// -- sort first by occurrences, then by variable number
int qcompare (const void * o1, const void * o2)
{
  int v1 = *(int*)o1;
  int v2 = *(int*)o2;
  
  int r = occurrences [v1] - occurrences [v2];
  
  return r == 0 ? v1 - v2 : r;
}


/*********************************************************************/
//quantify out all variables from min to max-1 from node and return
//the result. deref node.
/*********************************************************************/
tdd_node * Qelim(tdd_node * form,int min,int max)
{
  if (noqelim) return form;
  
  size_t theoryVarSize = theory->num_of_vars (theory);

  occurrences = NULL;
  
  printf ("QELIM: Initial size in nodes: %d\n", Cudd_DagSize (form));
  
  if (qelim_occur)
    {
      occurrences = (int*)malloc (sizeof (int) * theoryVarSize);
      memset (occurrences, 0, sizeof (int) * theoryVarSize);
      tdd_var_occurrences (tdd, form, occurrences);

      if (verbose)
	for (size_t i = 0; i < theoryVarSize; i++)
	  if (occurrences [i] != 0)
	    printf ("var %d occurs %d\n", i, occurrences [i]);
    }


  // -- number of variables to quantify out
  int qsize = max - min;
  int * qvars = (int*) malloc (sizeof (int) * qsize);
  
  // create an array with all variables that need to be quantified out
  for (int i = 0; i < qsize; i++)
    qvars [i] = min + i;

  if (qelim_occur)
    qsort (qvars, qsize, sizeof(int), qcompare);
  
  
  //printf ("QELIM: Initial size in paths: %d\n", tdd_path_size (tdd, form));

  //clear variable set
  memset(varSet,0,totalVarNum * sizeof(int));

  //now quantify out elements if using qelim1, or set the elements of
  //varSet to 1 if using qelim2
  for(int i = 0; i < qsize; i++) {
    if(qelim2) varSet[qvars [i]] = 1;
    else {
      printf ("QELIM of var: %d", qvars [i]);
      tdd_node *tmp = tdd_exist_abstract (tdd, form, qvars [i]);
      Cudd_Ref (tmp);
      Cudd_RecursiveDeref (cudd, form);
      form = tmp;
      printf (" size: %d\n", Cudd_DagSize (form));
    }
  }

  //quantify, if using qelim2
  if(qelim2) {
    tdd_node *tmp;

    if (qelim_approx)
      tmp = tdd_over_abstract (tdd, form, varSet);
    else
      tmp = tdd_exist_abstract_v2 (tdd, form, varSet);
    Cudd_Ref (tmp);
    Cudd_RecursiveDeref (cudd, form);
    form = tmp;
  }

  free (qvars); qvars = NULL;

  if (occurrences != NULL)
    {
      free (occurrences); 
      occurrences = NULL;
    }
  
      

  printf ("QELIM: Final size in nodes: %d\n", Cudd_DagSize (form));
  //printf ("QELIM: Final size in paths: %d\n", tdd_path_size (tdd, form));


  //all done
  return form;
}

/**********************************************************************
 * convert a formula to a tdd
 *********************************************************************/
tdd_node *ToTdd(smt_formula_t *f)
{
  tdd_node *res = NULL;
  //constraint -- we only accept weak inequalities
  if(f->type == SMT_CONS) {
    assert(!f->cons->strict);
    res = ConsToTdd(f->cons->coeffs[0],VarId(f->cons->vars[0]),
                    f->cons->coeffs[1],VarId(f->cons->vars[1]),f->cons->bound);
  } else if(f->type == SMT_AND) {
    res = ConstFormula(true);
    int i = 0;
    while(f->subs[i]) res = FormOp(res,ToTdd(f->subs[i++]),'&');
  } else if(f->type == SMT_OR) {
    res = ConstFormula(false);
    int i = 0;
    while(f->subs[i]) res = FormOp(res,ToTdd(f->subs[i++]),'|');
  } else if(f->type == SMT_NOT) {
    res = FormOp(ToTdd(f->subs[0]),NULL,'!');
  } else if(f->type == SMT_EXISTS || f->type == SMT_FORALL) {
    res = ToTdd(f->subs[0]);
    int min = INT_MAX,max = INT_MIN,i = 0;
    while(f->qVars[i]) {
      int v = VarId(f->qVars[i++]);
      min = (min < v) ? min : v;
      max = (max > v) ? max : v;
    }
    ++max;
    assert(min < max);
    res = Qelim(res,min,max);
  } else {
    printf("ERROR: illegal SMT formula type %d!\n",f->type);
    exit(1);
  }
  return res;
}

/*********************************************************************/
//recursively process a formula to determine the set of its variable
/*********************************************************************/
void FindVars(smt_formula_t *f,set<string> &vars)
{
  int i = 0;
  switch(f->type) {
  case SMT_CONS:
    vars.insert(f->cons->vars[0]);
    vars.insert(f->cons->vars[1]);
    break;
  case SMT_AND:
  case SMT_OR:
  case SMT_NOT:
    while(f->subs[i]) FindVars(f->subs[i++],vars);
    break;
  case SMT_EXISTS:
  case SMT_FORALL:    
    while(f->qVars[i]) vars.insert(f->qVars[i++]);
    FindVars(f->subs[0],vars);
    break;
  default:
    printf("ERROR: illegal SMT formula type %d!\n",f->type);
    exit(1);
  }
}

/**********************************************************************
 * the core solver routine
 *********************************************************************/
void Solve()
{
  //process each file
  for(list<string>::const_iterator it = fileNames.begin();it != fileNames.end();++it) {
    //parse SMT file. the AST will be stored in smtFormula
    yyin = fopen(it->c_str(),"r");
    if(!yyin) {
      fprintf(stderr,"ERROR: could not open SMT file %s for parsing!\n",it->c_str());
      exit(1);
    }
    yyparse();
    fclose(yyin);
  
    //find total number of variables in formula
    set<string> vars;
    FindVars(smtFormula,vars);

    totalVarNum = vars.size();
    varSet = new int [totalVarNum];
 
    //solve the formula
    CreateManagers();
    tdd_node *node = ToTdd(smtFormula);
  
    //check result
    if(node == ConstFormula(true)) printf("TRUE!\n");
    else if(node == ConstFormula(false)) printf("FALSE!\n");
    else printf("UNKNOWN!\n");

    //cleanup
    smt_destroy_formula(smtFormula);
    delete [] varSet;
    DestroyManagers();
  }
}

/**********************************************************************
 * the main routine
 *********************************************************************/
int main(int argc,char *argv[])
{
  ProcessInputs(argc,argv);
  Solve();
  return 0;
}

/**********************************************************************
 * end of smt_qelim_solver.c
 *********************************************************************/

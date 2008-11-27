#include <stdio.h>
#include <stdlib.h>

#include "smt_qelim_solver.h"
#include "smt_formula.h"

extern int yyparse(void);
extern smt_formula_t *smtFormula;
extern FILE *yyin;

/**********************************************************************
 * the core solver routine
 *********************************************************************/
int smt_qelim_solve(char *fileName,tdd_manager *tdd)
{
  //parse SMT file. the AST will be stored in smtFormula
  yyin = fopen(fileName,"r");
  if(!yyin) {
    fprintf(stderr,"ERROR: could not open SMT file %s for parsing!\n",fileName);
    exit(1);
  }
  yyparse();
  fclose(yyin);
  
  //solve the formula

  //cleanup
  smt_destroy_formula(smtFormula);

  return -1;
}

/**********************************************************************
 * the main routine
 *********************************************************************/
int main(int argc,char *argv[])
{
  return 0;
}

/**********************************************************************
 * end of smt_qelim_solver.c
 *********************************************************************/

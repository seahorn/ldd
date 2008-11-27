#include "smt_formula.h"

extern int yyparse(void);
extern smt_formula_t *smtFormula;

int main(void)
{
  yyparse ();
  smt_print_formula(stdout,smtFormula);
  printf("\n");
  smt_destroy_formula(smtFormula);
  return 0;
}



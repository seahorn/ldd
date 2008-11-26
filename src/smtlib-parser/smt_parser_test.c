#include "smt_formula.h"

extern int yyparse(void);
extern smt_formula_t *smtFormula;

int main(void)
{
  yyparse ();
  print_formula(stdout,smtFormula);
  destroy_formula(smtFormula);
  return 0;
}



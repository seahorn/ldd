/**
 * this file contains a set of utility routines used to manipulate
 * SMT-LIB formulas.
 */

#include <stdio.h>
#include <stdlib.h>
#include "smt_formula.h"

void destroy_cons(smt_cons_t *c)
{
  free(c->vars[0]);
  free(c->vars[1]);
}

void destroy_formula(smt_formula_t *f)
{
  int i = 0;
  switch(f->type) {
  case CONS:
    destroy_cons(f->cons);
    free(f->cons);
    break;
  case AND:
  case OR:
  case NOT:
    while(f->subs[i]) destroy_formula(f->subs[i++]);
    free(f->subs);
    break;
  case EXISTS:
  case FORALL:
    destroy_formula(f->subs[0]);
    free(f->subs);
    while(f->qVars[i]) free(f->qVars[i++]);
    free(f->qVars);
    break;
  default:
    printf("ERROR: illegal SMT formula type %d!\n",f->type);
    exit(1);
  }
  free(f);
}

void print_cons(FILE *out,smt_cons_t *c)
{
  fprintf(out,"((%d * %s) + (%d * %s) %s %d)",
          c->coeffs[0],c->vars[0],
          c->coeffs[1],c->vars[1],
          c->strict ? "<" : "<=",
          c->bound);
}

void print_formula(FILE *out,smt_formula_t *f)
{
  int i = 0;
  switch(f->type) {
  case CONS:
    print_cons(out,f->cons);
    break;
  case AND:
  case OR:
    fprintf(out,"(%s ",f->type == AND ? "and" : "or");
    for(;;) { 
      if(f->subs[i]) print_formula(out,f->subs[i++]); 
      else {
        fprintf(out,")");
        break;
      }
      if(f->subs[i]) fprintf(out," "); 
    }
    break;
  case NOT:
    fprintf(out,"(not ");
    print_formula(out,f->subs[0]);
    fprintf(out,")");
    break;
  case EXISTS:
  case FORALL:
    fprintf(out,"(%s (",f->type == EXISTS ? "exists" : "forall");
    for(;;) { 
      if(f->qVars[i]) fprintf(out,"%s",f->qVars[i++]); 
      else {
        fprintf(out,") ");
        break;
      }
      if(f->qVars[i]) fprintf(out," "); 
    }
    print_formula(out,f->subs[0]);
    fprintf(out,")");
    break;
  default:
    printf("ERROR: illegal SMT formula type %d!\n",f->type);
    exit(1);
  }
}

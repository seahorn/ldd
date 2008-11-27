/**
 * this file contains a set of utility routines used to manipulate
 * SMT-LIB formulas.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "smt_formula.h"

smt_formula_t *create_cons(int c1,char *v1,int c2,char *v2,int s,int b)
{
  smt_formula_t *res = malloc(sizeof(smt_formula_t));
  memset(res,0,sizeof(smt_formula_t));
  res->type = SMT_CONS;
  res->cons = malloc(sizeof(smt_cons_t));
  res->cons->coeffs[0] = c1;
  res->cons->coeffs[1] = c2;
  res->cons->vars[0] = strdup(v1);
  res->cons->vars[1] = strdup(v2);
  res->cons->strict = s;
  res->cons->bound = b;
  return res;
}

void destroy_cons(smt_cons_t *c)
{
  free(c->vars[0]);
  free(c->vars[1]);
}

void destroy_formula(smt_formula_t *f)
{
  int i = 0;
  switch(f->type) {
  case SMT_CONS:
    destroy_cons(f->cons);
    free(f->cons);
    break;
  case SMT_AND:
  case SMT_OR:
  case SMT_NOT:
    while(f->subs[i]) destroy_formula(f->subs[i++]);
    free(f->subs);
    break;
  case SMT_EXISTS:
  case SMT_FORALL:
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
  case SMT_CONS:
    print_cons(out,f->cons);
    break;
  case SMT_AND:
  case SMT_OR:
    fprintf(out,"(%s ",f->type == SMT_AND ? "and" : "or");
    for(;;) { 
      if(f->subs[i]) print_formula(out,f->subs[i++]); 
      else {
        fprintf(out,")");
        break;
      }
      if(f->subs[i]) fprintf(out," "); 
    }
    break;
  case SMT_NOT:
    fprintf(out,"(not ");
    print_formula(out,f->subs[0]);
    fprintf(out,")");
    break;
  case SMT_EXISTS:
  case SMT_FORALL:
    fprintf(out,"(%s (",f->type == SMT_EXISTS ? "exists" : "forall");
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

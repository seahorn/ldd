/**
 * this file contains a set of utility routines used to manipulate
 * SMT-LIB formulas.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "smt_formula.h"

/**********************************************************************
 * create an atomic constraint formula
 *********************************************************************/
smt_formula_t *smt_create_cons(int c1,char *v1,int c2,char *v2,int s,int b)
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

/**********************************************************************
 * destroy a constraint
 *********************************************************************/
void smt_destroy_cons(smt_cons_t *c)
{
  free(c->vars[0]);
  free(c->vars[1]);
}

/**********************************************************************
 * destroy a formula
 *********************************************************************/
void smt_destroy_formula(smt_formula_t *f)
{
  int i = 0;
  switch(f->type) {
  case SMT_CONS:
    smt_destroy_cons(f->cons);
    free(f->cons);
    break;
  case SMT_AND:
  case SMT_OR:
  case SMT_NOT:
    while(f->subs[i]) smt_destroy_formula(f->subs[i++]);
    free(f->subs);
    break;
  case SMT_EXISTS:
  case SMT_FORALL:
    smt_destroy_formula(f->subs[0]);
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

/**********************************************************************
 * print a constraint
 *********************************************************************/
void smt_print_cons(FILE *out,smt_cons_t *c)
{
  char c1[64],c2[64],b[64];

  if(c->coeffs[0] < 0) snprintf(c1,64,"(~ %d)",-(c->coeffs[0]));
  else snprintf(c1,64,"%d",c->coeffs[0]);

  if(c->coeffs[1] < 0) snprintf(c2,64,"(~ %d)",-(c->coeffs[1]));
  else snprintf(c2,64,"%d",c->coeffs[1]);

  if(c->bound < 0) snprintf(b,64,"(~ %d)",-(c->bound));
  else snprintf(b,64,"%d",c->bound);

  fprintf(out,"(%s (+ (* %s %s) (* %s %s)) %s)",
          c->strict ? "<" : "<=",
          c1,c->vars[0],c2,c->vars[1],b);
}

/**********************************************************************
 * print a formula
 *********************************************************************/
void smt_print_formula(FILE *out,smt_formula_t *f)
{
  int i = 0;
  switch(f->type) {
  case SMT_CONS:
    smt_print_cons(out,f->cons);
    break;
  case SMT_AND:
  case SMT_OR:
    fprintf(out,"(%s ",f->type == SMT_AND ? "and" : "or");
    for(;;) { 
      if(f->subs[i]) smt_print_formula(out,f->subs[i++]); 
      else {
        fprintf(out,")");
        break;
      }
      if(f->subs[i]) fprintf(out," "); 
    }
    break;
  case SMT_NOT:
    fprintf(out,"(not ");
    smt_print_formula(out,f->subs[0]);
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
    smt_print_formula(out,f->subs[0]);
    fprintf(out,")");
    break;
  default:
    printf("ERROR: illegal SMT formula type %d!\n",f->type);
    exit(1);
  }
}

/**********************************************************************
 * renames old with new in f in-place
 *********************************************************************/
void smt_rename_var(smt_formula_t *f,char *old,char *sub)
{
  int i = 0;
  switch(f->type) {
  case SMT_CONS:
    for(;i < 2;++i) {
      if(!strcmp(f->cons->vars[i],old)) {
        free(f->cons->vars[i]);
        f->cons->vars[i] = strdup(sub);
      }
    }
    break;
  case SMT_AND:
  case SMT_OR:
  case SMT_NOT:
    while(f->subs[i]) smt_rename_var(f->subs[i++],old,sub);
    break;
  case SMT_EXISTS:
  case SMT_FORALL:    
    while(f->qVars[i]) { 
      if(!strcmp(f->qVars[i],old)) {
        free(f->qVars[i]);
        f->qVars[i] = strdup(sub);
      }
      ++i;
    }
    smt_rename_var(f->subs[0],old,sub);
    break;
  default:
    printf("ERROR: illegal SMT formula type %d!\n",f->type);
    exit(1);
  }
}

/**********************************************************************
 * end of smt_formula.c
 *********************************************************************/

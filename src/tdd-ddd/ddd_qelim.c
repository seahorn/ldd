#include "tdd-dddInt.h"

static void ddd_pop_qelim_stack (ddd_qelim_context_t *ctx); 

/**********************************************************************
 * functions for incremental quantifier elimination
 *********************************************************************/

qelim_context_t* 
ddd_qelim_init (tdd_manager *tdd, bool *vars)
{
  ddd_qelim_context_t *res;
  int vn;
  int i;
  
  res = (ddd_qelim_context_t*) malloc (sizeof (ddd_qelim_context_t));
  res->tdd = tdd;
  
  vn = tdd->theory->num_of_vars (tdd->theory); 
  res->vars = (bool*)malloc(vn * sizeof(bool));
  
  for(i = 0;i < vn; i++) 
    res->vars[i] = vars[i];

  res->stack = NULL;

  return (qelim_context_t*)res;
}






void 
ddd_qelim_destroy_context(qelim_context_t* context)
{
  ddd_qelim_context_t *ctx = (ddd_qelim_context_t*)context;

  if (ctx->vars != NULL)
    free(ctx->vars);
  
  if (ctx->stack != NULL)
    while (ctx->stack)
      ddd_pop_qelim_stack (ctx);

  free(ctx);
}


lincons_t 
ddd_qelim_pop(qelim_context_t* context)
{
  ddd_qelim_context_t *ctx = (ddd_qelim_context_t*)context;

  /* check for stack emptiness */
  if(ctx->stack == NULL) return NULL;

  /* get the constraint for the top element */
  lincons_t res = (lincons_t)(ctx->stack->cons);


  ddd_pop_qelim_stack (ctx);
  

  /* all done, return what was poped */
  return res;
}

/**
 * Pop an element from the qelim stack. Destroys a DBM if needed
 */
void 
ddd_pop_qelim_stack (ddd_qelim_context_t *ctx)
{
  ddd_qelim_stack_t * next;
  
  if (ctx->stack == NULL) return;

  next = ctx->stack->next;
  
  
  /* check if we need to get rid of the DBM. Successive stack elements
     may have the same DBM. We only need to destroy the last
     reference */
  if (ctx->stack->dbm != NULL)
    if (next == NULL || (ctx->stack->dbm != next->dbm))
      dbm_destory (ctx->stack->dbm);

  free (ctx->stack);

  ctx->stack = next;  
}


void 
ddd_qelim_push(qelim_context_t* context, lincons_t l)
{
  ddd_qelim_context_t *ctx;

  /*  new stack element */
  ddd_qelim_stack_t *new_stack;

  ctx =  (ddd_qelim_context_t*)context;

  new_stack = (ddd_qelim_stack_t*) malloc (sizeof (ddd_qelim_stack_t));

  /* XXX no good error handling */
  assert (new_stack != NULL);

  /* store the constraint */
  new_stack->cons = (ddd_cons_t*)l;


  

  /* if current context is unsat, record what was pushed and terminate */
  if (ctx->stack && ctx->stack->dbm->unsat)
    {
      new_stack->dbm = NULL;
      new_stack->next = ctx->stack;
      ctx->stack = new_stack;
      return;
    }
  

  /* check if this is the first entry, then create a DBM 
     with a single constraint. Don't bother checking its closure.
  */
  if (ctx->stack == NULL)
    new_stack->dbm = dbm_create_init (new_stack->cons->term.var1, 
					new_stack->cons->term.var2,
					new_stack->cons->cst.int_val);
  else
    {
      /* create a new DBM using the newly pushed constraint */
      new_stack->dbm = dbm_update_entry_close (ctx->stack->dbm, 
					       new_stack->cons->term.var1,
					       new_stack->cons->term.var2,
					       new_stack->cons->cst.int_val);
      
      /* close above takes care of the closure */
      /* new constraint was really new, so need to run floyd-warshall again */
/*       if (new_stack->dbm != ctx->stack->dbm) */
/*       	dbm_floyd_warshal (new_stack->dbm); */
    }
  

  /* wire the new element onto the stack */
  new_stack->next = ctx->stack;
  ctx->stack = new_stack;
}

tdd_node * 
ddd_qelim_solve (qelim_context_t* context)
{
  ddd_qelim_context_t *ctx = (ddd_qelim_context_t*)context;
  ddd_qelim_stack_t *stack = ctx->stack;


  /* if stack is NULL, then no constraints were added */
  if (stack == NULL) return tdd_get_true (ctx->tdd);

  /* check for UNSAT */
  if(stack->dbm == NULL || stack->dbm->unsat) return tdd_get_false (ctx->tdd);


  /* the constraints are SAT. Eliminate variables and create a TDD of
     the result */

  assert (stack->dbm != NULL);
  assert (stack->dbm->closed);
  
  {
    tdd_node *res = tdd_get_true(ctx->tdd);
    dbm_t *dbm = ctx->stack->dbm;
    int i,j;


    cuddRef (res);
    
    for (i = 0; i < dbm->width; i++)
      {
	/* check that the variable is not quantified out */
	if (ctx->vars [dbm->mindim + i]) continue;
	
	for (j = 0; j < dbm->width; j++)
	  {
	    ddd_cons_t cons;
	    tdd_node *tmp, *tmp2;
	    
	    /* ignore the diagonal */
	    if (i == j) continue;
	    
	    /* check that the variable is not quantified out */
	    if (ctx->vars [dbm->mindim + j]) continue;
	    
	    /* check that there is a constraint */
	    if (DBM_CEL (dbm, i, j).inf) continue;
	    
	    /* XXX For correctness, only need to produce a set of
	       constraints that are logically equivalent to a
	       DBM. There are many choices here */


	    /* create a constraint by hand */
	    cons.term.var1 = dbm->mindim + i;
	    cons.term.var2 = dbm->mindim + j;
	    cons.cst.type = DDD_INT;
	    cons.cst.int_val = DBM_CEL (dbm, i, j).val;
	    cons.strict = 0;
	    
	    /* create tdd for the constraint */
	    tmp = ctx->tdd->theory->to_tdd (ctx->tdd, (lincons_t) (&cons));
	    cuddRef (tmp);
	    
	    /* Accumulate into result */
	    tmp2 = tdd_and (ctx->tdd, res, tmp);
	    cuddRef (tmp2);
	    Cudd_IterDerefBdd (ctx->tdd->cudd, tmp);
	    Cudd_IterDerefBdd (ctx->tdd->cudd, res);

	    res = tmp2;
	  }
      }

    cuddDeref (res);
    return res;
  }
}

    

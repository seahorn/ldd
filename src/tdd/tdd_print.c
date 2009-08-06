#include "util.h"
#include "tddInt.h"

static void tdd_print_minterm_aux (tdd_manager *tdd, tdd_node *node, int* list);


/**
 * Prints disjoint sum of product cover for the function. Based on
 * Cudd_PrintMinterm
 */
int
tdd_print_minterm (tdd_manager *tdd, tdd_node* node)
{
  int i, *list;
  DdNode *zero;
  
  zero = Cudd_Not(DD_ONE(CUDD));
  
  list = ALLOC(int,CUDD->size);
  if (list == NULL)
    {
      CUDD->errorCode = CUDD_MEMORY_OUT;
      return 0;
    }
  
  for (i = 0; i < CUDD->size; i++) list[i] = 2;
  tdd_print_minterm_aux (tdd, node, list);
  FREE(list);
  return (1);
  
}


static void 
tdd_print_minterm_aux (tdd_manager *tdd, tdd_node *n, int* list)
{
  DdNode *N, *Nv, *Nnv;
  int i, v, index, p;
  
  
  N = Cudd_Regular (n);
  
  if (cuddIsConstant (N))
    {
      /* n == N here implies that n is one */
      if (n == N) 
	{
	  for (i = 0; i < CUDD->size; i++)
	    {
	      p = CUDD->invperm [i];
	      v = list [p];
	      if (v != 2 && tdd->ddVars [p] == NULL) 
		fprintf (stderr, "%sb%d", (v == 0 ? "!" : " "), p);
	      else if (v == 0) 
		{
		  fprintf (CUDD->out, "!(");
		  THEORY->print_lincons (CUDD->out, 
					 tdd->ddVars [p]);
		  fprintf (CUDD->out, ") ");
		}
	      else if (v == 1)
		{
		  THEORY->print_lincons (CUDD->out, 
					 tdd->ddVars [p]);
		  fprintf (CUDD->out, " ");
		}
	    }
	  fprintf (CUDD->out, "\n");
	}
    } 
  else
    {
      Nv = Cudd_NotCond (cuddT(N), N != n);
      Nnv = Cudd_NotCond (cuddE(N), N != n);
      index = N->index;
      list[index] = 0;
      tdd_print_minterm_aux (tdd, Nnv, list);
      list[index] = 1;
      tdd_print_minterm_aux (tdd, Nv, list);
      list[index] = 2;
    }
  return;
}

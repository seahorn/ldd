#include "util.h"
#include "dddCuddInt.h"


int main (void)
{
  DdManager * cudd;
  dddManager * ddd;
  
  unsigned int nvars, nslots;
  unsigned int cacheSize, maxMemory;
  
  nvars = 0;
  cacheSize = 127;
  maxMemory = 0;
  nslots = CUDD_UNIQUE_SLOTS;

  printf ("Hey, I compile and run\n");  

  cudd = Cudd_Init (nvars, 0, nslots, cacheSize, maxMemory);

  printf ("Even created cudd with %p\n", cudd);  
  

  ddd = dddCudd_Init (cudd, 4);

  printf ("And DDD manager  %p\n", ddd);  

  
  {
    DdNode *n, *n2, *n3, *n4, *n5, *n6, *n7, *n8, *n9;
    
    n = dddCons (ddd, 1, 2, 3);
    Cudd_Ref (n);
    assert (ddd->ddVars [n->index] != NULL);

    printf ("The first variable is at index %d\n", n->index);

    Cudd_PrintDebug (ddd->cudd, n, 4, 4);

    n2 = dddCons (ddd, 3, 2, 1);
    Cudd_Ref (n2);
    Cudd_PrintDebug (ddd->cudd, n2, 4, 4);

    n3 = dddAnd (ddd, n, n2);
    Cudd_Ref (n3);
    Cudd_PrintDebug (ddd->cudd, n3, 4, 4);

    n4 = dddOr (ddd, n, n2);
    Cudd_Ref (n4);
    Cudd_PrintDebug (ddd->cudd, n4, 4, 4);
    

    n5 = dddCons (ddd, 1, 2, 5);
    Cudd_Ref (n5);
    Cudd_PrintDebug (ddd->cudd, n5, 4, 4);

    /* XXX No vinfo record was created for this variable! XXX */
    assert (ddd->ddVars [n5->index] != NULL);
    

    n6 = dddAnd (ddd, n, n5);
    Cudd_Ref (n6);
    Cudd_PrintDebug (ddd->cudd, n6, 4, 4);


  }
  

  return 0;
}

#include "util.h"
#include "lddInt.h"


/**
   \brief Creates a new LDD manager.

   \param t theory for managing labels of nodes
   \return a pointer to the manager if successful; NULL otherwise
   
   \sa Cudd_Init(), and Ldd_Quit()
 */
LddManager * 
Ldd_Init (DdManager *cudd, theory_t * t)
{
  LddManager* ldd;
  int i;
  
  ldd = ALLOC(LddManager, 1);
  if (ldd == NULL) return 0;
  

  /* set CUDD and theory */
  ldd->cudd = cudd;
  ldd->theory = t;

  ldd->existsAbstract = Ldd_ExistsAbstractFM;

  ldd->be_bddlike = 0;

  /* allocate the map from DD nodes to linear constraints*/
  ldd->varsSize = cudd->maxSize;
  ldd->ddVars = ALLOC(lincons_t,ldd->varsSize);
  if (ldd->ddVars == NULL)
    {
      FREE(ldd);
      return 0;
    }
  for (i = 0; i < ldd->varsSize; i++)
    ldd->ddVars [i] = NULL;

  /* add a hook to fix MTR tree after variable reordering */
  Cudd_AddHook (CUDD, &lddFixMtrTree, CUDD_POST_REORDERING_HOOK);
  
  return ldd;
}

/**
   \brief Deletes resources allocated with DD manager.
   
   \sa Cudd_Quit(), and Ldd_Quit()
 */
void 
Ldd_Quit (LddManager * ldd)
{
  if (ldd->ddVars != NULL)
    {
      int i;
      for (i = 0; i < ldd->varsSize; i++)
	if (ldd->ddVars [i] != NULL)
	  {
	    THEORY->destroy_lincons (ldd->ddVars [i]);
	    ldd->ddVars [i] = NULL;
	  }
     
      FREE (ldd->ddVars);
      ldd->ddVars = NULL;
    }
  FREE (ldd);
}



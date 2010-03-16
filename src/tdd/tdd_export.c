#include <stdio.h>

#include "util.h"
#include "tddInt.h"

static void ddClearFlag(LddNode * n);
static int lddDumpSmtLibV1BodyRecur (FILE *, LddManager*, LddNode*, char**);

/**
   \brief Writes an SMT-LIB version 1 representing the argument LDD
   
   Returns 1 on in case of success; 0 otherwise; Does not close the
   file.
 */
int
Ldd_DumpSmtLibV1 (LddManager *ldd,
		  LddNode *f,
		  char **vnames, /* variable names (or NULL) */
		  char *bname,
		  FILE *fp)
{
  /* variables in the support of the diagram */
  int* occurrences;
  int retval;
  int nvars = THEORY->num_of_vars (THEORY);
  int brkt, i;
  
  occurrences = ALLOC (int,nvars);
  if (occurrences == NULL)
    {
      CUDD->errorCode = CUDD_MEMORY_OUT;
      goto failure;
    }

  memset (occurrences, 0, sizeof(int) * nvars);
  Ldd_VarOccurrences (ldd, f, occurrences);

  retval = fprintf (fp, "(benchmark ");
  if (retval == EOF) goto failure;
  
  if (bname != NULL)
    retval = fprintf (fp, "%s\n", bname);
  else
    retval = fprintf (fp, "ldd_%p\n", f);
  if (retval == EOF) goto failure;


  retval = THEORY->dump_smtlibv1_prefix (THEORY, fp, occurrences);
  if (retval == 0) goto failure;

  FREE (occurrences);
  occurrences = NULL;
  
  retval = fprintf (fp, ":formula\n");
  if (retval == EOF) goto failure;
  
  brkt = lddDumpSmtLibV1BodyRecur (fp, ldd, Cudd_Regular (f), vnames);
  ddClearFlag (f);

  if (brkt < 0) goto failure;

  if (Cudd_IsComplement (f))
    {
      retval = fprintf (fp, " (not ");
      if (retval == EOF) goto failure;
    }

#if SIZEOF_VOID_P == 8
  retval = fprintf (fp, " $l%lx", 
		    (ptruint) Cudd_Regular (f) / (ptruint) sizeof(LddNode));
#else
  retval = fprintf (fp, " $l%x", 
		    (ptruint) Cudd_Regular (f) / (ptruint) sizeof(LddNode));
#endif
  if (retval == EOF) goto failure;
  

  if (Cudd_IsComplement (f))
    {
      retval = fprintf (fp, ")");
      if (retval == EOF) goto failure;
    }    

  /* print closing brackets */
  for (i = 0; i < brkt; i++)
    {
      retval = fprintf (fp, ")");
      if (retval == EOF) goto failure;
    }

  retval = fprintf (fp, ")");
  if (retval == EOF) goto failure;

  return 1;
  
 failure: 
  if (occurrences != NULL)
    FREE (occurrences);
  return (0);
  
  
}

/**
 * Adapted from cuddUtil.c
 */
static void
ddClearFlag(LddNode * n)
{
    if (!Cudd_IsComplement(n->next)) {
	return;
    }
    /* Clear visited flag. */
    n->next = Cudd_Regular(n->next);
    if (cuddIsConstant(n)) {
	return;
    }
    ddClearFlag(cuddT(n));
    ddClearFlag(Cudd_Regular(cuddE(n)));
    return;

}


int
lddDumpSmtLibV1BodyRecur (FILE *fp, 
			  LddManager *ldd, 
			  LddNode *F,
			  char **vnames)
{
  
  int retval;
  LddNode *fv, *fnv;

  int brktT, brktE;

  
  
  if (F == DD_ONE(CUDD) || Cudd_IsComplement (F->next)) return 0;

  /* mark as visited */
  F->next = Cudd_Not (F->next);

  fv = cuddT(F);
  fnv = cuddE (F);

  brktT = lddDumpSmtLibV1BodyRecur (fp, ldd, fv, vnames);
  if (brktT < 0) return brktT;
  
  brktE = lddDumpSmtLibV1BodyRecur (fp, ldd, Cudd_Regular (fnv), vnames);
  if (brktE < 0) return brktE;
  


#if SIZEOF_VOID_P == 8
  retval = fprintf (fp, "(flet ($l%lx (if_then_else ", 
		    (ptruint) F / (ptruint) sizeof(LddNode));
#else
  retval = fprintf (fp, "(flet ($l%x (if_then_else ", 
		    (ptruint) F / (ptruint) sizeof(LddNode));
#endif
  if (retval == EOF) return -1;
  
  retval = THEORY->print_lincons_smtlibv1 (fp, lddC (ldd, F->index), vnames);
  if (retval == 0) return -1;

  if (cuddIsConstant (fv))
    /* fv is never complemented */
    retval = fprintf (fp, " true ");
  else
    {
#if SIZEOF_VOID_P == 8
      retval = fprintf (fp, " $l%lx ", 
			(ptruint) fv / (ptruint) sizeof(LddNode));
#else
      retval = fprintf (fp, " $l%x ",
      			(ptruint) fv / (ptruint) sizeof(LddNode));
#endif
    }
  if (retval == EOF) return -1;

  if (Cudd_IsConstant (fnv))
    {
      retval = fprintf (fp, Cudd_IsComplement (fnv) ? "false " : "true ");
      if (retval == EOF) return -1;
    }
  else
    {
      if (Cudd_IsComplement (fnv))
	{
	  retval = fprintf (fp, "(not ");
	  if (retval == EOF) return -1;
	}

#if SIZEOF_VOID_P == 8
      retval = 
	fprintf (fp, "$l%lx ", 
		 (ptruint) Cudd_Regular (fnv) / (ptruint) sizeof(LddNode));
#else
      retval = 
	fprintf (fp, "$l%x ", 
		 (ptruint) Cudd_Regular (fnv) / (ptruint) sizeof(LddNode));
#endif
      if (retval == EOF) return -1;
     
      if (Cudd_IsComplement (fnv))
	{
	  retval = fprintf (fp, ")");
	  if (retval == EOF) return -1;
	}
    }
  

  retval = fprintf (fp, ")) ");
  if (retval == EOF) return -1;  
  
  return brktT + brktE + 1;  
}

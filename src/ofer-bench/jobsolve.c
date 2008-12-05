 #include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <limits.h>

#include "util.h"
#include "cudd.h"
#include "tdd.h"
#include "tdd-ddd.h"

extern void yyparse (void);

extern  DdManager *cudd;
extern  tdd_manager* tdd;
extern  theory_t *t;


extern int bench_max;
extern tdd_node* bench;

extern FILE* yyin;


int limit = INT_MAX;
int qelim_mode = 1;
int expected = 2;
int order = 1;

int verbose = 0;

static tdd_node *qelim1 ();
static tdd_node *qelim2 ();
static tdd_node *qelim3 ();
static tdd_node *qelim4 ();
static tdd_node *qelim5 ();


int write_tdd (char* filename, DdManager *cudd, tdd_node *f, char** inames)
{
  FILE* file;
  int res;
  
  file = fopen (filename, "w+");
  res = Cudd_DumpDaVinci(cudd, 1, &f, inames, NULL, file);
  fclose (file);
  return res;
  
}

/**
   jobsolve
     
    -e mode         existential quantification mode. 
                      1  use tdd_exist_abstract
                      2  use tdd_exist_abstract_v2 
                      3  use tdd_exist_abstract_v2 one var at a time

    -m max          the maximum for the job schedule

    -r res          expected result, res can be 0, 1, or 2

    -l lim          maximum number of variables to eliminate

    -o order        elimination order for one-at-a-time quantification
                      1 ascending starting from the second variale
                      2 descending starting from the last variable
		      3 ascending starting from the first variable

    -v              Verbose debug/sanity mode. 		      
		      
 */

void usage ()
{
  printf ("jobsolve [-e mode] [-m max] "
	  "[-r res] [-l lim] [-o order] [-v] problem\n");

  printf ("  -e mode\texistential quantification mode\n "
	  "\t\t 1 tdd_exist_abstract,\n\t\t 2 tdd_exist_abstract_v2\n"
	  "\t\t 3 tdd_exist_abstract_v2 one var at a time\n"
	  "\t\t 4 tdd_exist_abstract with tdd_sat_reduce\n"
	  "\t\t 5 tdd_exist_abstract_v2 one var at a time "
	  "with tdd_sat_reduce\n");

  printf ("  -m max\tthe maximum for the job schedule\n");

  printf ("  -r res\texpected result (0 FALSE, 1 TRUE, 2 ANYTHING)\n");

  printf ("  -l lim\tmaximum number of variables to eliminate\n");

  printf ("  -o order\tvariable elimination order\n"
	  "\t\t 1 ascending starting from var 1\n"
	  "\t\t 2 descending starting from last var\n"
	  "\t\t 3 ascending starting from var 0\n");

  printf ("  -v\tverbose debug mode\n");	  
  printf (" problem\tproblem file\n");
  abort ();
}

int main (int argc, char** argv)
{
  size_t size;
  int c;
  tdd_node * res;
  
  while ((c = getopt (argc, argv, "o:e:m:r:l:v")) != -1)
    {
      switch (c)
	{
	case 'e':
	  qelim_mode = atoi (optarg);
	  break;

	case 'm':
	  bench_max = atoi (optarg);
	  break;

	case 'r':
	  expected = atoi (optarg);
	  break;

	case 'l':
	  limit = atoi (optarg);
	  if (limit < 0)
	    limit = INT_MAX;
	  break;
	  
	case 'o':
	  order = atoi (optarg);
	  break;


	case 'v':
	  verbose = 1;
	  break;
	  
	case '?':
	  usage ();
	  return 1;
	default:
	  usage ();
	}      
    }

  if (optind >= argc)
    {
      fprintf (stderr, "No benchmark file specified\n");
      usage ();
    }
  

  printf ("Starting with max_bench=%d with %s\n", bench_max, argv[optind]);
  yyin = fopen (argv[optind], "r");
  if (yyin == NULL)
    {
      perror ("Can't open problem file");
      abort ();
    }
  

  //  yydebug = 1;
  yyparse ();
  fclose (yyin);
  printf ("Parsing ended with DD of size %d\n", Cudd_DagSize (bench));

  

  if (verbose)
    {
      fprintf (stderr, "MANAGER DEBUG DUMP\n");
      tdd_manager_debug_dump (tdd);
      fprintf (stderr, "THEORY DEBUG DUMP\n");
      t->theory_debug_dump (tdd);
    }
  

  size = t->num_of_vars (t);
  printf ("Using %d numeric variables\n", size);

  
  if (verbose)
    {
      printf ("Writing initial diagram:\n");
      /*       Cudd_PrintMinterm (cudd, bench); */
      write_tdd ("initial.dot", cudd, bench, NULL);
    }
  

  printf ("Starting existential quantification: %d\n", qelim_mode);

  switch (qelim_mode)
    {
    case 1:
      res = qelim1 ();
      break;
    case 2:
      res = qelim2 ();
      break;
    case 3:
      res = qelim3 ();
      break;
    case 4:
      res = qelim4 ();
      break;
    case 5:
      res = qelim5 ();
      break;
    default:
      printf ("Unknown QELIM mode: %d\n", qelim_mode);
      abort ();    
    }
  

  if (tdd_get_false (tdd) == res)
    printf ("FALSE\n");
  else if (tdd_get_true (tdd) == res)
    printf ("TRUE\n");
  else
    printf ("SOME TDD\n");

  if (expected == 0 && tdd_get_false (tdd) == res)
    printf ("GOOD: got FALSE as expected\n");
  else if (expected == 1 && tdd_get_true (tdd) == res)
    printf ("GOOD: got TRUE as expected\n");
  else if (expected == 2)
    printf ("GOOD: didn't crash as expected\n");
  else
    {
      char *s1, *s2;
      
      if (expected == 0) s1 = "FALSE";
      else if (expected == 1) s1 = "TRUE";
      else s1 = "NOTHING";
      
      if (tdd_get_true (tdd) == res)
	s2 = "TRUE";
      else if (tdd_get_false (tdd) == res)
	s2 = "FALSE";
      else s2 = "NON-EMPTY-TDD";	
      
      printf ("BAD: expected %s, got %s\n", s1, s2);
      return 1;
    }
  
  return 0;

  if (verbose)
    util_print_cpu_stats (stderr);
}

tdd_node *
qelim1 ()
{
  
  tdd_node *res;
  unsigned int i;
  size_t size;

  /* number of variables that were eliminated */
  size_t count;

  /* elimination order: go from start to end using step */
  unsigned int start, end, step;

  size = t->num_of_vars (t);

  switch (order)
    {
    case 1:
      /* ascending start from the second variable */
      step = 1;
      start = 1;
      end = size;
      break;
    case 2:
      step = -1;
      start = size - 1;
      end = 0;
      break;
    case 3:
      /* ascending starting from the first variable */
      step = 1;
      start = 0;
      end = size;
      break;
    default:
      printf ("Unknown elimination order %d\n", order);
      abort ();
    }
  
  
  
  
  res = bench;

  for (i = start, count=0; i != end && count < limit; i+=step,count++)
    {
      tdd_node* tmp;
      char name[20];

      /* Only run quantification when needed */
      if (Cudd_IsConstant (res)) break;

      tmp = tdd_exist_abstract (tdd, res, i);
      Cudd_Ref (tmp);
      Cudd_RecursiveDeref (cudd, res);
      res = tmp;

      printf ("After quantifying x%d the size is %d\n",
	      i, Cudd_DagSize (res));

      if (verbose)
	{
	  printf ("Sanity check:\n");
	  tdd_sanity_check (tdd);


	  printf ("Writting current result\n");
	  /* /\*       Cudd_PrintMinterm (cudd, res); *\/ */
	  snprintf (name, 20, "qelim-%d.dot", i);
	  write_tdd (name, cudd, res, NULL);

	  tdd_manager_debug_dump (tdd);
	  t->theory_debug_dump (tdd);
	

	  printf ("The result of existential quantification is: ");
	  if (Cudd_ReadOne (cudd) == res)
	    printf ("true\n");
	  else if (Cudd_ReadLogicZero (cudd) == res)
	    printf ("false\n");
	  else
	    {
	      printf ("NON-EMPTY\n");
/* 	      Cudd_PrintMinterm (cudd, res); */
	    }
	}
    }

  return res;
}


tdd_node *
qelim2 ()
{
  tdd_node *res, *tmp;
  size_t i;
  size_t size;

  /* variables to be quantified out */
  bool *vars;


  size = t->num_of_vars (t);  
  
  vars = (bool*) malloc (sizeof(bool) * size);
  for (i = 0; i < size; i++)
    vars [i] = 1;
  
  res = bench;

  if (Cudd_IsConstant (res)) return res;
  
  tmp = tdd_exist_abstract_v2 (tdd, res, vars);
  Cudd_Ref (tmp);
  Cudd_RecursiveDeref (cudd, res);
  res = tmp;
  
  return res;
}


tdd_node *
qelim3 ()
{
  tdd_node *res;
  unsigned int i;
  size_t size;

  /* variables to be quantified out */
  bool *vars;

  /* number of variables that were eliminated */
  size_t count;

  /* elimination order: go from start to end using step */
  unsigned int start, end, step;

  size = t->num_of_vars (t);

  switch (order)
    {
    case 1:
      /* ascending start from the second variable */
      step = 1;
      start = 1;
      end = size;
      break;
    case 2:
      step = -1;
      start = size - 1;
      end = 0;
      break;
    case 3:
      /* ascending starting from the first variable */
      step = 1;
      start = 0;
      end = size;
      break;
    default:
      printf ("Unknown elimination order %d\n", order);
      abort ();
    }
  
  
  vars = (bool*) malloc (sizeof(bool) * size);
  for (i = 0; i < size; i++)
    vars [i] = 0;
  
  
  res = bench;

  for (i = start, count=0; i != end && count < limit; i+=step,count++)
    {
      tdd_node* tmp;
      char name[20];

      /* Only run quantification when needed */
      if (Cudd_IsConstant (res)) break;

      vars [i] = 1;
      tmp = tdd_exist_abstract_v2 (tdd, res, vars);
      vars [i] = 0;
      
      Cudd_Ref (tmp);
      Cudd_RecursiveDeref (cudd, res);
      res = tmp;

      printf ("After quantifying x%d the size is %d\n",
	      i, Cudd_DagSize (res));

      if (verbose)
	{
	  printf ("Sanity check:\n");
	  tdd_sanity_check (tdd);


	  printf ("Writting current result\n");
	  /* /\*       Cudd_PrintMinterm (cudd, res); *\/ */
	  snprintf (name, 20, "qelim-%d.dot", i);
	  write_tdd (name, cudd, res, NULL);

	  tdd_manager_debug_dump (tdd);
	  t->theory_debug_dump (tdd);
	

	  printf ("The result of existential quantification is: ");
	  if (Cudd_ReadOne (cudd) == res)
	    printf ("true\n");
	  else if (Cudd_ReadLogicZero (cudd) == res)
	    printf ("false\n");
	  else
	    {
	      printf ("NON-EMPTY\n");
	    }
	}
    }

  return res;
 }
 

tdd_node *
qelim4 ()
{
  
  tdd_node *res;
  unsigned int i;
  size_t size;

  /* number of variables that were eliminated */
  size_t count;

  /* elimination order: go from start to end using step */
  unsigned int start, end, step;

  size = t->num_of_vars (t);

  switch (order)
    {
    case 1:
      /* ascending start from the second variable */
      step = 1;
      start = 1;
      end = size;
      break;
    case 2:
      step = -1;
      start = size - 1;
      end = 0;
      break;
    case 3:
      /* ascending starting from the first variable */
      step = 1;
      start = 0;
      end = size;
      break;
    default:
      printf ("Unknown elimination order %d\n", order);
      abort ();
    }
  
  
  
  
  res = bench;

  for (i = start, count=0; i != end && count < limit; i+=step,count++)
    {
      tdd_node* tmp;
      char name[20];
      int szBefore, szAfter;

      /* Only run quantification when needed */
      if (Cudd_IsConstant (res)) break;

/*       printf ("Is SAT: %d\n", tdd_is_sat (tdd, res)); */
/*       printf ("UNSAT size: %d\n", tdd_unsat_size (tdd, res)); */

      szBefore = Cudd_DagSize (res);
      tmp = tdd_sat_reduce (tdd, res, -1);
      Cudd_Ref (tmp);
      Cudd_RecursiveDeref (cudd, res);
      res = tmp;
      szAfter = Cudd_DagSize (res);
      if (szBefore != szAfter)
	printf ("\tReduced from %d to %d\n", szBefore, szAfter);
      

      tmp = tdd_exist_abstract (tdd, res, i);
      Cudd_Ref (tmp);
      Cudd_RecursiveDeref (cudd, res);
      res = tmp;

      printf ("After quantifying x%d the size is %d\n",
	      i, Cudd_DagSize (res));

      if (verbose)
	{
	  printf ("Sanity check:\n");
	  tdd_sanity_check (tdd);


	  printf ("Writting current result\n");
	  /* /\*       Cudd_PrintMinterm (cudd, res); *\/ */
	  snprintf (name, 20, "qelim-%d.dot", i);
	  write_tdd (name, cudd, res, NULL);

	  tdd_manager_debug_dump (tdd);
	  t->theory_debug_dump (tdd);
	

	  printf ("The result of existential quantification is: ");
	  if (Cudd_ReadOne (cudd) == res)
	    printf ("true\n");
	  else if (Cudd_ReadLogicZero (cudd) == res)
	    printf ("false\n");
	  else
	    {
	      printf ("NON-EMPTY\n");
/* 	      Cudd_PrintMinterm (cudd, res); */
	    }
	}
    }

  return res;
}



tdd_node *
qelim5 ()
{
  tdd_node *res;
  unsigned int i;
  size_t size;

  /* variables to be quantified out */
  bool *vars;

  /* number of variables that were eliminated */
  size_t count;

  /* elimination order: go from start to end using step */
  unsigned int start, end, step;

  size = t->num_of_vars (t);

  switch (order)
    {
    case 1:
      /* ascending start from the second variable */
      step = 1;
      start = 1;
      end = size;
      break;
    case 2:
      step = -1;
      start = size - 1;
      end = 0;
      break;
    case 3:
      /* ascending starting from the first variable */
      step = 1;
      start = 0;
      end = size;
      break;
    default:
      printf ("Unknown elimination order %d\n", order);
      abort ();
    }
  
  
  vars = (bool*) malloc (sizeof(bool) * size);
  for (i = 0; i < size; i++)
    vars [i] = 0;
  
  
  res = bench;

  for (i = start, count=0; i != end && count < limit; i+=step,count++)
    {
      tdd_node* tmp;
      char name[20];


      int szBefore, szAfter;

      /* Only run quantification when needed */
      if (Cudd_IsConstant (res)) break;


      szBefore = Cudd_DagSize (res);
      tmp = tdd_sat_reduce (tdd, res, -1);
      Cudd_Ref (tmp);
      Cudd_RecursiveDeref (cudd, res);
      res = tmp;
      szAfter = Cudd_DagSize (res);
      if (szBefore != szAfter)
	printf ("\tReduced from %d to %d\n", szBefore, szAfter);



      vars [i] = 1;
      tmp = tdd_exist_abstract_v2 (tdd, res, vars);
      vars [i] = 0;
      
      Cudd_Ref (tmp);
      Cudd_RecursiveDeref (cudd, res);
      res = tmp;

      printf ("After quantifying x%d the size is %d\n",
	      i, Cudd_DagSize (res));

      if (verbose)
	{
	  printf ("Sanity check:\n");
	  tdd_sanity_check (tdd);


	  printf ("Writting current result\n");
	  /* /\*       Cudd_PrintMinterm (cudd, res); *\/ */
	  snprintf (name, 20, "qelim-%d.dot", i);
	  write_tdd (name, cudd, res, NULL);

	  tdd_manager_debug_dump (tdd);
	  t->theory_debug_dump (tdd);
	

	  printf ("The result of existential quantification is: ");
	  if (Cudd_ReadOne (cudd) == res)
	    printf ("true\n");
	  else if (Cudd_ReadLogicZero (cudd) == res)
	    printf ("false\n");
	  else
	    {
	      printf ("NON-EMPTY\n");
	    }
	}
    }

  return res;
 }
 

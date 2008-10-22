%{

  #include <stdio.h>
  
  #include "util.h"
  #include "cudd.h"
  #include "tdd.h"
  #include "tdd-ddd.h"

  #define YYERROR_VERBOSE

  

  void yyerror (char *s);
  int yylex (void);

  DdManager *cudd;
  tdd_manager* tdd;
  theory_t *t;

  tdd_node *bench;

  int bench_max = 0;

%}

%union
{
  int ival;
  tdd_node* nval;
}


%locations
%debug

%token VARS_TOK
%token COL_TOK
%token MISSING_TOK
%token MAX_TOK
%token NL_TOK
%token <ival> NUMERAL_TOK
%token LBRACKET_TOK
%token RBRACKET_TOK
%token MINUS_TOK

%type <ival> var
%type <ival> constant
%type <nval> constraint
%type <nval> clause
%type <nval> cnf


%start bench

%%

bench: prefix NL_TOK cnf {bench = $3};

prefix: VARS_TOK COL_TOK NUMERAL_TOK 
        {
	  cudd = Cudd_Init (0, 0, CUDD_UNIQUE_SLOTS, 127, 0);
	  t = ddd_create_int_theory ($3+1);
	  tdd = tdd_init (cudd, t);
	  printf ("Created universe with %d variables\n", t->num_of_vars (t));
        };


cnf: 
      cnf clause
      {
	$$ = tdd_and (tdd, $1, $2);
	Cudd_Ref ($$);
	Cudd_RecursiveDeref (cudd, $1);
	Cudd_RecursiveDeref (cudd, $2);
      }
    | clause
    ;

clause:
         constraint clause
         {
           $$ = tdd_or (tdd, $1, $2);
	   Cudd_Ref ($$);
	   Cudd_RecursiveDeref (cudd, $1);
	   Cudd_RecursiveDeref (cudd, $2);
         }

       | constraint NL_TOK { $$ = $1;}
       ;

constraint: var var constant 
{
  constant_t cst;
  linterm_t term;
  lincons_t cons;
  size_t size;
  /* coefficients */
  int* cf;

  size = t->num_of_vars (t);
  cf = (int*) malloc (sizeof(int) * size);
  memset (cf, 0, sizeof(int)* size);
  cf [$1] = 1;
  cf [$2] = -1;
  
  cst = t->create_int_cst ($3);
  term = t->create_linterm (cf, size);
  cons = t->create_cons (term, 0, cst);

  $$ = to_tdd (tdd, cons);
  Cudd_Ref ($$);
}

;

var:   
       NUMERAL_TOK {$$ = $1 + 1; }
     | MISSING_TOK {$$ = 0;}

  
     ;

constant: 
          NUMERAL_TOK 
	  |    LBRACKET_TOK MAX_TOK MINUS_TOK NUMERAL_TOK RBRACKET_TOK
{
  $$ = bench_max - $4;
}

     ;


%%
void yyerror (char *s)
{
  fprintf (stderr, "%s\n", s);
}


int main (int argc, char** argv)
{
  size_t size;
  int i;
  tdd_node* res;

  if (argc != 2)
    bench_max = 50;
  else
    bench_max = atoi (argv [1]);
  
  printf ("Benchmark with max_bench=%d\n", bench_max);

  //  yydebug = 1;
  yyparse ();
  printf ("Parsing ended with %p, of size %d\n", 
	  bench, Cudd_DagSize (bench));

  //tdd_manager_debug_dump (tdd);
  

  size = t->num_of_vars (t);
  printf ("Using %d DD variables\n", size);


  printf ("Starting existential quantification\n");
  res = bench;

  //for (i = size - 1 ; i >= 0; i--)
  for (i = 0; i < size ; i++)
    {
      /* Only run quantification when needed */
      if (Cudd_IsConstant (res)) break;

      res = tdd_exist_abstract (tdd, res, i);
      Cudd_Ref (res);
      printf ("After quantifying x%d the size is %d\n", 
	      i, Cudd_DagSize (res));
    }
  
  printf ("The result of existential quantification is: ");
  if (Cudd_ReadOne (cudd) == res)
    printf ("true\n");
  else if (Cudd_ReadLogicZero (cudd) == res)
    printf ("false\n");
  else
    {
      printf ("\n");
      Cudd_PrintMinterm (cudd, res); 
    }
  
  return 0;
}


%{

  /** 
   * this parser only accepts quantified boolean combinations of TVPI
   * constraints. we are assuming that TVPI constraints will be of the
   * form CX + DY {<,<=} K. the parser will only accept constraints of
   * this form, so even difference constraints must be expressed as
   * (1*X) + (-1*Y) {<,<=} K.
   */

  #include <stdio.h>
  #include <stdlib.h>
  #include <string.h>
  #include <assert.h>
  #include "smt_formula.h"

  #define YYERROR_VERBOSE

  /* functions defined by the lexer and parser */ 
  void yyerror (char *s);
  int yylex (void);

  /** the last token read */
  extern char *lastTok;

  /** the final AST */
  smt_formula_t *smtFormula = NULL;
%}

%locations
%debug

%union {
  int ival;
  char *str;
  char **strptr;
  struct smt_formula *fptr;
  struct smt_formula **fpptr;
}

%token BVNUMERAL_TOK BVBINNUMERAL_TOK BVHEXNUMERAL_TOK
%token NUMERAL_TOK RATIONAL_TOK
%token AND_TOK OR_TOK NOT_TOK SYM_TOK
%token VAR_TOK FVAR_TOK
%token STRING_TOK LT_TOK LE_TOK STAR_TOK PLUS_TOK MINUS_TOK 
%token NEG_TOK AR_SYMB USER_VAL_TOK
%token EXISTS_TOK FORALL_TOK
%token LET_TOK FLET_TOK
%token SORTS_TOK FUNS_TOK PREDS_TOK
%token EXTENSIONS_TOK DEFINITION_TOK
%token AXIOMS_TOK LOGIC_TOK COLON_TOK
%token LPAREN_TOK RPAREN_TOK
%token LSQBRACKET_TOK RSQBRACKET_TOK
%token SAT_TOK UNSAT_TOK UNKNOWN_TOK
%token ASSUMPTION_TOK FORMULA_TOK
%token STATUS_TOK BENCHMARK_TOK
%token EXTRASORTS_TOK EXTRAFUNS_TOK EXTRAPREDS_TOK
%token LANGUAGE_TOK DOLLAR_TOK QUESTION_MARK_TOK
%token EQUALS_TOK SEMICOLON_TOK

%type<ival> numeral number quant_symb
%type<str> var fvar variable tvpi_var fun_symb basic_term quant_var
%type<strptr> quant_vars
%type<fptr> tvpi_cons an_term an_formula
%type<fpptr> an_terms

%start benchmark

%%

benchmark:
    LPAREN_TOK BENCHMARK_TOK bench_name bench_attributes RPAREN_TOK
    ;

bench_name: SYM_TOK { free(lastTok); }
;

bench_attributes:
      bench_attribute bench_attributes 
    | bench_attribute 
      ;

bench_attribute:
    COLON_TOK ASSUMPTION_TOK an_formula 
{
  printf("ERROR: assumptions not supported!\n");
  exit(1);
}
    | COLON_TOK FORMULA_TOK an_formula 
{
  smtFormula = $3;
  printf ("Saw a formula!\n");
}

  | COLON_TOK STATUS_TOK status 
  | COLON_TOK LOGIC_TOK logic_name 
  | COLON_TOK EXTRASORTS_TOK LPAREN_TOK sort_symb_decls RPAREN_TOK { }
  | COLON_TOK EXTRAFUNS_TOK LPAREN_TOK fun_symb_decls RPAREN_TOK { }
  | COLON_TOK EXTRAPREDS_TOK LPAREN_TOK pred_symb_decls RPAREN_TOK { }
  | annotation 
  ;

logic_name:
  SYM_TOK { free(lastTok); }
| SYM_TOK parameters { free(lastTok); }
;

status:
    SAT_TOK 
  | UNSAT_TOK 
  | UNKNOWN_TOK 
    ;

sort_symbs:
    sort_symb sort_symbs
  | sort_symb 
  ;

sort_symb_decls:
    sort_symb_decls sort_symb_decl
  | sort_symb_decl 
  ;


fun_symb_decls:
    fun_symb_decls fun_symb_decl 
  | fun_symb_decl 
    ;



fun_symb_decl:
  LPAREN_TOK fun_symb sort_symbs annotations RPAREN_TOK { if($2) free($2); }
| LPAREN_TOK fun_symb sort_symbs RPAREN_TOK { if($2) free($2); }
;

pred_symb_decls:
    pred_symb_decls pred_symb_decl 
  | pred_symb_decl
    ;

pred_symb_decl:
    LPAREN_TOK fun_symb sort_symbs annotations RPAREN_TOK { if($2) free($2); }
  | LPAREN_TOK fun_symb annotations RPAREN_TOK { if($2) free($2); }
  | LPAREN_TOK fun_symb sort_symbs RPAREN_TOK { if($2) free($2); }
  | LPAREN_TOK fun_symb RPAREN_TOK { if($2) free($2); }
    ;

an_formula:
    an_term 
    ;

/* we are storing the variable list as a NULL-terminated array of
   char* */
quant_vars:
/* base case */
quant_var {
  $$ = malloc(2 * sizeof(char*));
  $$[0] = $1;
  $$[1] = NULL;
}
/* concatenate */
| quant_vars quant_var {
  int i = 0,j = 0;
  while($1[i]) ++i;
  $$ = malloc((i + 2) * sizeof(char*));
  for(;j < i;++j) $$[j] = $1[j];
  $$[i] = $2;
  $$[i+1] = NULL;
  free($1);
}
;

quant_var: 
  LPAREN_TOK variable sort_symb RPAREN_TOK { $$ = $2; }
;

/** we use 0 for exists and 1 for forall */
quant_symb:
  EXISTS_TOK { $$ = 0; }
| FORALL_TOK { $$ = 1; }
;

an_terms:
/* base case */
an_term {
  $$ = malloc(2 * sizeof(char*));
  $$[0] = $1;
  $$[1] = NULL;
}
/* concatenate */
| an_terms an_term {
  int i = 0,j = 0;
  while($1[i]) ++i;
  $$ = malloc((i + 2) * sizeof(char*));
  for(;j < i;++j) $$[j] = $1[j];
  $$[i] = $2;
  $$[i+1] = NULL;
  free($1);
}
;

sort_symb_decl: simple_identifier 
;

sort_symb: identifier 
;

an_term:
  tvpi_cons { $$ = $1; }
  /* boolean */
| LPAREN_TOK AND_TOK an_terms RPAREN_TOK {
  assert($3[0] && $3[1]);
  $$ = malloc(sizeof(smt_formula_t));
  memset($$,0,sizeof(smt_formula_t));
  $$->type = AND;
  $$->lhs = $3[0];
  $$->rhs = $3[1];
  int i = 2;
  while($3[i]) {
    smt_formula_t *x = malloc(sizeof(smt_formula_t));
    memset(x,0,sizeof(smt_formula_t));
    x->type = AND;
    x->lhs = $$;
    x->rhs = $3[i++];
    $$ = x;
  }
  free($3);
}
| LPAREN_TOK OR_TOK an_terms RPAREN_TOK {
  assert($3[0] && $3[1]);
  $$ = malloc(sizeof(smt_formula_t));
  memset($$,0,sizeof(smt_formula_t));
  $$->type = OR;
  $$->lhs = $3[0];
  $$->rhs = $3[1];
  int i = 2;
  while($3[i]) {
    smt_formula_t *x = malloc(sizeof(smt_formula_t));
    memset(x,0,sizeof(smt_formula_t));
    x->type = OR;
    x->lhs = $$;
    x->rhs = $3[i++];
    $$ = x;
  }
  free($3);
}
| LPAREN_TOK NOT_TOK an_term RPAREN_TOK {
  $$ = malloc(sizeof(smt_formula_t));
  memset($$,0,sizeof(smt_formula_t));
  $$->type = NOT;
  $$->lhs = $3;
  $$->rhs = NULL;
}
  /* quantify */
| LPAREN_TOK quant_symb quant_vars an_term annotations RPAREN_TOK {
  $$ = malloc(sizeof(smt_formula_t));
  memset($$,0,sizeof(smt_formula_t));
  $$->type = $2 ? FORALL : EXISTS;
  $$->lhs = $4;
  $$->qVars = $3;
}
| LPAREN_TOK quant_symb quant_vars an_term RPAREN_TOK {
  $$ = malloc(sizeof(smt_formula_t));
  memset($$,0,sizeof(smt_formula_t));
  $$->type = $2 ? FORALL : EXISTS;
  $$->lhs = $4;
  $$->qVars = $3;
}
  /* parenthesis */
| LPAREN_TOK an_term RPAREN_TOK { $$ = $2; }
  /* rest are unsupported -- these are needed for general SMT but not
     needed right now */ 
| basic_term { 
  printf("ERROR: basic_term not supported!\n");
  exit(1);
}
| LPAREN_TOK basic_term annotations RPAREN_TOK { 
  printf("ERROR: basic_term not supported!\n");
  exit(1);
}
| LPAREN_TOK fun_symb an_terms annotations RPAREN_TOK {
  printf("ERROR: fun_symb not supported!\n");
  exit(1);
}
| LPAREN_TOK fun_symb an_terms RPAREN_TOK {
  printf("ERROR: fun_symb not supported!\n");
  exit(1);
}
| LPAREN_TOK let_decl an_formula annotations RPAREN_TOK {
  printf("ERROR: let not supported!\n");
  exit(1);
}
| LPAREN_TOK let_decl an_formula RPAREN_TOK {
  printf("ERROR: let not supported!\n");
  exit(1);
}
| LPAREN_TOK flet_decl an_formula annotations RPAREN_TOK {
  printf("ERROR: flet not supported!\n");
  exit(1);
}
| LPAREN_TOK flet_decl an_formula RPAREN_TOK { 
  printf("ERROR: flet not supported!\n");
  exit(1);
}
;

/** 
 * we are assuming that TVPI constraints will be of the form CX + DY
 * {<,<=} K. the parser will only accept constraints of this form, so
 * even difference constraints must be expressed as (1*X) + (-1*Y)
 * {<,<=} K.
*/
tvpi_cons : 
LPAREN_TOK LT_TOK 
  LPAREN_TOK PLUS_TOK 
    LPAREN_TOK STAR_TOK numeral tvpi_var RPAREN_TOK 
    LPAREN_TOK STAR_TOK numeral tvpi_var RPAREN_TOK 
  RPAREN_TOK
  numeral 
RPAREN_TOK {
  $$ = malloc(sizeof(smt_formula_t));
  memset($$,0,sizeof(smt_formula_t));
  $$->type = CONS;
  $$->cons = malloc(sizeof(smt_cons_t));
  $$->cons->coeffs[0] = $7;
  $$->cons->coeffs[1] = $12;
  $$->cons->vars[0] = $8;
  $$->cons->vars[1] = $13;
  $$->cons->strict = 1;
  $$->cons->bound = $16;
}
| LPAREN_TOK LE_TOK 
    LPAREN_TOK PLUS_TOK 
      LPAREN_TOK STAR_TOK numeral tvpi_var RPAREN_TOK 
      LPAREN_TOK STAR_TOK numeral tvpi_var RPAREN_TOK 
    RPAREN_TOK 
    numeral 
  RPAREN_TOK {
  $$ = malloc(sizeof(smt_formula_t));
  memset($$,0,sizeof(smt_formula_t));
  $$->type = CONS;
  $$->cons = malloc(sizeof(smt_cons_t));
  $$->cons->coeffs[0] = $7;
  $$->cons->coeffs[1] = $12;
  $$->cons->vars[0] = $8;
  $$->cons->vars[1] = $13;
  $$->cons->strict = 0;
  $$->cons->bound = $16;
}
;

tvpi_var:
  SYM_TOK { $$ = lastTok; }
| var { $$ = $1; }
;

let_decl:
  LET_TOK LPAREN_TOK var an_term RPAREN_TOK { free($3); }
;

flet_decl:
  FLET_TOK LPAREN_TOK fvar an_term RPAREN_TOK { free($3); }
;

basic_term:
  var { $$ = $1; }
| fvar { $$ = $1; }
| numeral {}
| rational {}
| fun_symb { $$ = $1; }
;


annotations:
  annotation annotations 
| annotation 
;

annotation:
  attribute 
| attribute user_value 
;

user_value:
  USER_VAL_TOK
| STRING_TOK
;

fun_symb:
  identifier { $$ = NULL; }
| AR_SYMB { $$ = lastTok; }
;

attribute: COLON_TOK SYM_TOK { free(lastTok); };

rational: RATIONAL_TOK { 
  printf("ERROR: rational not supported!\n");
  exit(1);
};

numeral:
  number { $$ = $1; }
  /* assuming that ~ means unary minus */
| LPAREN_TOK NEG_TOK numeral RPAREN_TOK { $$ = -($3); }
| BVNUMERAL_TOK {
  printf("ERROR: bv numerals not supported!\n");
  exit(1);
}
| BVNUMERAL_TOK parameters {
  printf("ERROR: bv numerals not supported!\n");
  exit(1);
}
| BVBINNUMERAL_TOK {
  printf("ERROR: bvbin numerals not supported!\n");
  exit(1);
}
| BVHEXNUMERAL_TOK {
  printf("ERROR: bvhex numerals not supported!\n");
  exit(1);
}
;

number: NUMERAL_TOK { 
  $$ = atoi(lastTok);
  free(lastTok);
}
;

parameter_list:
  number {}
| number COLON_TOK parameter_list {}
;

parameters: LSQBRACKET_TOK parameter_list RSQBRACKET_TOK
;

variable:
    var { $$ = $1; }
  | fvar { $$ = $1; }
 ;

var: VAR_TOK { $$ = lastTok; };

fvar: FVAR_TOK { $$ = lastTok; };

identifier: 
   simple_identifier
  | indexed_identifier 
  ;
  
indexed_identifier: simple_identifier parameters;

simple_identifier: SYM_TOK { free(lastTok); };

%%

void yyerror (char *s)
{
  yydebug = 1;
  fprintf (stderr, "Here: %s\n", s);
}


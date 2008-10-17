%{
  #include <stdio.h>

 #define YYERROR_VERBOSE

  void yyerror (char *s);

%}

%locations
%debug

%token BVNUMERAL_TOK
%token BVBINNUMERAL_TOK
%token BVHEXNUMERAL_TOK
%token NUMERAL_TOK
%token RATIONAL_TOK
%token SYM_TOK
%token VAR_TOK
%token FVAR_TOK
%token STRING_TOK
%token AR_SYMB
%token USER_VAL_TOK
%token EXISTS_TOK
%token FORALL_TOK
%token LET_TOK
%token FLET_TOK
%token SORTS_TOK
%token FUNS_TOK
%token PREDS_TOK
%token EXTENSIONS_TOK
%token DEFINITION_TOK
%token AXIOMS_TOK
%token LOGIC_TOK
%token COLON_TOK
%token LPAREN_TOK
%token RPAREN_TOK
%token LSQBRACKET_TOK
%token RSQBRACKET_TOK
%token SAT_TOK
%token UNSAT_TOK
%token UNKNOWN_TOK
%token ASSUMPTION_TOK
%token FORMULA_TOK
%token STATUS_TOK
%token BENCHMARK_TOK
%token EXTRASORTS_TOK
%token EXTRAFUNS_TOK
%token EXTRAPREDS_TOK
%token LANGUAGE_TOK
%token DOLLAR_TOK
%token QUESTION_MARK_TOK
%token EQUALS_TOK
%token SEMICOLON_TOK


%start benchmark


%%

benchmark:
    LPAREN_TOK BENCHMARK_TOK bench_name bench_attributes RPAREN_TOK
    ;

bench_name:
    SYM_TOK 
    ;

bench_attributes:
      bench_attribute bench_attributes 
    | bench_attribute 
      ;

bench_attribute:
    COLON_TOK ASSUMPTION_TOK an_formula 
    | COLON_TOK FORMULA_TOK an_formula 
{
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
    SYM_TOK
  | SYM_TOK parameters 
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
    LPAREN_TOK fun_symb sort_symbs annotations RPAREN_TOK
  | LPAREN_TOK fun_symb sort_symbs RPAREN_TOK
    ;

pred_symb_decls:
    pred_symb_decls pred_symb_decl 
  | pred_symb_decl
    ;

pred_symb_decl:
    LPAREN_TOK fun_symb sort_symbs annotations RPAREN_TOK
  | LPAREN_TOK fun_symb annotations RPAREN_TOK
  | LPAREN_TOK fun_symb sort_symbs RPAREN_TOK
  | LPAREN_TOK fun_symb RPAREN_TOK
    ;


an_formula:
    an_term 
    ;

quant_vars:
    quant_vars quant_var 
  | quant_var 
    ;

quant_var: 
    LPAREN_TOK variable sort_symb RPAREN_TOK
    ;

quant_symb:
    EXISTS_TOK 
  | FORALL_TOK 
    ;

an_terms:
    an_term an_terms 
  | an_term 
    ;

sort_symb_decl:
  simple_identifier 
  ;

sort_symb:
  identifier 
  ;

an_term:
    basic_term 
  | LPAREN_TOK basic_term annotations RPAREN_TOK 
  | LPAREN_TOK fun_symb an_terms annotations RPAREN_TOK
  | LPAREN_TOK fun_symb an_terms RPAREN_TOK
  | LPAREN_TOK quant_symb quant_vars an_term annotations RPAREN_TOK
  | LPAREN_TOK quant_symb quant_vars an_term RPAREN_TOK
  | LPAREN_TOK let_decl an_formula annotations RPAREN_TOK
  | LPAREN_TOK let_decl an_formula RPAREN_TOK
  | LPAREN_TOK flet_decl an_formula annotations RPAREN_TOK
  | LPAREN_TOK flet_decl an_formula RPAREN_TOK
  | LPAREN_TOK an_term RPAREN_TOK
    ;


let_decl:
  LET_TOK LPAREN_TOK var an_term RPAREN_TOK
  ;

flet_decl:
  FLET_TOK LPAREN_TOK fvar an_term RPAREN_TOK
  ;

basic_term:
    var 
  | fvar 
  | numeral
  | rational
  | fun_symb 
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
    identifier
  | AR_SYMB
    ;

attribute:
    COLON_TOK SYM_TOK 
    ;
rational:
  RATIONAL_TOK
  ;

numeral:
    number
  | BVNUMERAL_TOK 
  | BVNUMERAL_TOK parameters 
  | BVBINNUMERAL_TOK 
  | BVHEXNUMERAL_TOK
    ;


number:
  NUMERAL_TOK ;

parameter_list:
    number
  | number COLON_TOK parameter_list
    ;

parameters: 
   LSQBRACKET_TOK parameter_list RSQBRACKET_TOK
  ;


variable:
    var 
  | fvar
 ;


var: VAR_TOK ;

fvar: FVAR_TOK ;

identifier: 
   simple_identifier
  | indexed_identifier 
  ;
  
indexed_identifier: simple_identifier parameters;

simple_identifier: SYM_TOK ;

%%

void yyerror (char *s)
{
  yydebug = 1;
  fprintf (stderr, "Here: %s\n", s);
}

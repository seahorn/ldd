/**
 Matched text is in yytext. 
 Length of yytext is yyleng.
 Semantic value of a token goes to yyval
*/

%{
  #include <string.h>
  #include "smt_parser.tab.h"
  
  /** function needed by the lexer */
  void yyerror (char*);

  /** buffer used to store the last token on the stack */
  char *lastTok = NULL;
%}

%option nounput
%option noyywrap

%%

"exists" { return EXISTS_TOK;}

"forall" { return FORALL_TOK;}

"let"  {return LET_TOK;}

"flet" {return FLET_TOK;}

"\""([^\"]|"\\\"")*"\"" { /* strdup yytext into token */ return STRING_TOK; }

"{"([^{}]|"\\}"|"\\{")*"}" { return USER_VAL_TOK; }

"sorts" {return SORTS_TOK;}
"funs" {return FUNS_TOK;}
"preds" {return PREDS_TOK;}
"extensions" {return EXTENSIONS_TOK;}
"definition" {return DEFINITION_TOK;}
"axioms" {return AXIOMS_TOK;}
"logic" {return LOGIC_TOK;}
":" {return COLON_TOK;}
"(" {return LPAREN_TOK;}
")" {return RPAREN_TOK;}
"[" {return LSQBRACKET_TOK;}
"]" {return RSQBRACKET_TOK;}
"sat" {return SAT_TOK;}
"unsat" {return UNSAT_TOK;}
"unknown" {return UNKNOWN_TOK;}
"assumption" {return ASSUMPTION_TOK;}
"formula" {return FORMULA_TOK;}
"status" {return STATUS_TOK;}
"benchmark" {return BENCHMARK_TOK;}
"extrasorts" {return EXTRASORTS_TOK;}
"extrafuns" {return EXTRAFUNS_TOK;}
"extrapreds" {return EXTRAPREDS_TOK;}
"language" {return LANGUAGE_TOK;}
";"[^"\n"]*"\n"  /* do nothing */;
"\n"  /* do nothing */;
"<" { return LT_TOK; }
"<=" { return LE_TOK; }
"*" { return STAR_TOK; }
"~" { return NEG_TOK; }
"+" { return PLUS_TOK; }
"-" { return MINUS_TOK; }
[=<>&@#\\+\-*/%|~]+ {lastTok = strdup(yytext); return AR_SYMB;} 
[0-9]+"."[0-9]+ {lastTok = strdup(yytext); return RATIONAL_TOK;}
[0-9]+ {lastTok = strdup(yytext); return NUMERAL_TOK;}
"bv"[0-9]+ {return BVNUMERAL_TOK;}
"bvbin"[0-1]+ {return BVBINNUMERAL_TOK;}
"bvhex"[0-9A-F]+ {return BVHEXNUMERAL_TOK;}
"?"[a-zA-Z][a-zA-Z._'0-9]* {lastTok = strdup(yytext); return VAR_TOK;}
"$"[a-zA-Z][a-zA-Z._'0-9]* {lastTok = strdup(yytext); return FVAR_TOK;}
"and" { return AND_TOK;}
"or" { return OR_TOK;}
"not" { return NOT_TOK;}
[a-zA-Z][a-zA-Z._\\0-9]* {lastTok = strdup(yytext); return SYM_TOK;}
[ \t\r] {};


%%


  

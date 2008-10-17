/**
 Matched text is in yytext. 
 Length of yytext is yyleng.
 Semantic value of a token goes to yyval
*/

%{
 #include "smt_parser.tab.h"

 void yyerror (char*);
%}

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
[=<>&@#\\+\-*/%|~]+ {return AR_SYMB;} 
[0-9]+"."[0-9]+ {return RATIONAL_TOK;}
[0-9]+ {return NUMERAL_TOK;}
"bv"[0-9]+ {return BVNUMERAL_TOK;}
"bvbin"[0-1]+ {return BVBINNUMERAL_TOK;}
"bvhex"[0-9A-F]+ {return BVHEXNUMERAL_TOK;}
"?"[a-zA-Z][a-zA-Z._'0-9]* {return VAR_TOK;}
"$"[a-zA-Z][a-zA-Z._'0-9]* {return FVAR_TOK;}
[a-zA-Z][a-zA-Z._\\0-9]* {return SYM_TOK;}
[ \t\r] {};


%%


  

%{
  #include "util.h"
  #include "cudd.h"
  #include "tdd.h"
  #include "tdd-ddd.h"

  #include "parser.tab.h"



  void yyerror (char*);
%}

%%
"variables" { return VARS_TOK; }
":"     {return COL_TOK;}
"M"     {return MISSING_TOK; }
"MAX"   {return MAX_TOK;}
"("     {return LBRACKET_TOK;}
")"     {return RBRACKET_TOK;}
"-"     {return MINUS_TOK;}

  

[\r\n]+      {return NL_TOK;}
[ \t]   {}

-?[0-9]+ { yylval.ival = atoi (yytext); return NUMERAL_TOK; }

.        { yyerror ("Unexpected character"); }

  


%%

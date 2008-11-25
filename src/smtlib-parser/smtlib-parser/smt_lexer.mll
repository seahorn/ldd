{
(*
This file is part of the SMT-LIB parser
Copyright (C) 2004-2005,2007-2008
              The University of Iowa

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*)

(* smt_lexer.mll *)

open Smt_parser
open Lexing

}
rule token = parse
  | "exists" {EXISTS_TOK}
  | "forall" {FORALL_TOK}
  | "let" {LET_TOK}
  | "flet" {FLET_TOK}
  | '"' ([^ '"'] | "\\\"")* '"' {
      let s = Lexing.lexeme lexbuf in
      let rec count_newlines i c =
        try 
          let i2 = String.index_from s i '\n' in
          count_newlines (i2+1) (c+1)
        with Not_found ->
          c
      in
      let newlines = count_newlines 0 0 in 
      let pos = lexbuf.lex_curr_p in
      lexbuf.lex_curr_p <- {pos with pos_lnum = pos.pos_lnum + newlines};
      STRING_TOK(s)
    }
  | '{' ([^ '{' '}'] | "\\}" | "\\{")* '}' {
      let s = Lexing.lexeme lexbuf in
      let rec count_newlines i c =
        try 
          let i2 = String.index_from s i '\n' in
          count_newlines (i2+1) (c+1)
        with Not_found ->
          c
      in
      let newlines = count_newlines 0 0 in 
      let pos = lexbuf.lex_curr_p in
      lexbuf.lex_curr_p <- {pos with pos_lnum = pos.pos_lnum + newlines};
      USER_VAL_TOK(s)
    }
  | "sorts" {SORTS_TOK}
  | "funs" {FUNS_TOK}
  | "preds" {PREDS_TOK}
  | "extensions" {EXTENSIONS_TOK}
  | "definition" {DEFINITION_TOK}
  | "axioms" {AXIOMS_TOK}
  | "logic" {LOGIC_TOK}
  | ':' {COLON_TOK}
  | '(' {LPAREN_TOK}
  | ')' {RPAREN_TOK}
  | '[' {LSQBRACKET_TOK}
  | ']' {RSQBRACKET_TOK}
  | "sat" {SAT_TOK}
  | "unsat" {UNSAT_TOK}
  | "unknown" {UNKNOWN_TOK}
  | "assumption" {ASSUMPTION_TOK}
  | "formula" {FORMULA_TOK}
  | "status" {STATUS_TOK}
  | "benchmark" {BENCHMARK_TOK}
  | "extrasorts" {EXTRASORTS_TOK}
  | "extrafuns" {EXTRAFUNS_TOK}
  | "extrapreds" {EXTRAPREDS_TOK}
  | "language" {LANGUAGE_TOK}
  | ';' [^'\n']* "\n" {
      let pos = lexbuf.lex_curr_p in
      lexbuf.lex_curr_p <- {pos with pos_lnum = pos.pos_lnum + 1};
      token lexbuf
    }  
  | '\n' {
      let pos = lexbuf.lex_curr_p in
      lexbuf.lex_curr_p <- {pos with pos_lnum = pos.pos_lnum + 1};
      token lexbuf
    }
  | ['=' '<' '>' '&' '@' '#' '\\' '+' '-' '*' '/' '%' '|' '~']+ {AR_SYMB(Lexing.lexeme lexbuf)}
  | ['0'-'9']+ "." ['0'-'9']+ {RATIONAL_TOK(Lexing.lexeme lexbuf)}
  | ['0'-'9']+ {NUMERAL_TOK(Lexing.lexeme lexbuf)}
  | "bv"['0'-'9']+ {BVNUMERAL_TOK(Lexing.lexeme lexbuf)}
  | "bvbin"['0'-'1']+ {BVBINNUMERAL_TOK(Lexing.lexeme lexbuf)}
  | "bvhex"['0'-'9' 'A' - 'F']+ {BVHEXNUMERAL_TOK(Lexing.lexeme lexbuf)}
  | '?' ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '.' '_' '\'' '0'-'9']* {VAR_TOK(Lexing.lexeme lexbuf)}
  | '$' ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '.' '_' '\'' '0'-'9']* {FVAR_TOK(Lexing.lexeme lexbuf)}
  | ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '.' '_' '\'' '0'-'9']* {SYM_TOK(Lexing.lexeme lexbuf)}
  | [' ' '\t' '\r'] {token lexbuf}
  | eof   {EOF_TOK}
  | _ {token lexbuf}



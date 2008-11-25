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

(** Main module. Parses a single benchmark file, then prints out the AST. *)

open Types
open Support
open Smt_parser
open Smt_lexer
open Printing

(** {6 Functions} *)

(** Parses the benchmark and prints out the AST. *)
let parse_benchmark file =
  let in_ch = open_in file in
  let lexbuf = Lexing.from_channel in_ch in
  let bench = 
    try
      Smt_parser.benchmark Smt_lexer.token lexbuf 
    with x ->
      let pos = lexbuf.Lexing.lex_curr_p in
      let line = pos.Lexing.pos_lnum in
      let s = Lexing.lexeme lexbuf in
      Printf.printf "Parsing error: line %d (%s)\n" line s;
      raise x
 in
  close_in in_ch;
  Printing.print_bench bench

let _ =
  let usage_msg = "smtbench <filename>" in
  let speclist = [] in
  Arg.parse speclist parse_benchmark usage_msg

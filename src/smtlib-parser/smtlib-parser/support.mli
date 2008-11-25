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

(** AST generation and type checking functions for the parser. *)

open Types

(** {6 Exceptions} *)

(** [TypeMismatch] exception (raised also by {!Smt_parser}). *)
exception TypeMismatch of string

(** {6 Functions} *)

(** Default sort name for numerals. Set by {!Signature.load_logic_signature}. *)
val numeral_sort : symbol_name ref

(** Default indices for the numeral sort. Set by {!Signature.load_logic_signature}. *)
val numeral_sort_indices : index_values ref

(** If given an empty list, it returns the default numeral sort (indices included); otherwise, it returns the actual parameter in the place of the default index values. *)
val get_numeral_sort : index_values -> sort_name * index_values

(** Declares a theory-defined sort. *)
val declare_base_sort : sort_name -> unit

(** Declares a user-defined sort. Raises a {!SortRedeclaration} exception if the sort is already declared (either theory- or  user-defined). *)
val declare_sort : sort_name -> unit

(** Declares a theory-defined function symbol. No sanity checks because a reasoner would be needed to catch ambiguities amongs theory-defined function declarations. *)
val declare_base_fun : symbol_name * sig_decl -> unit

(** Declares a user-defined function symbol. Raises {!TypeMismatch} exception if one of the following conditions is satisfied: {ul {li There is a theory-defined function with the same name and the same codomain sort names (index values are excluded from the comparison);} {li A user-defined function (previously defined) has the same name and the same codomain sorts (included their index values).}} *)
val declare_fun : return_type -> sig_decl -> unit

(** Converts a list of pairs [(]{!Types.sort_name}[ * ]{!Types.index_values}[)] into a function declaration. For example, the list [[[("BitVec",1),8];[("BitVec",1),4]]] corresponding to the function [f: BitVec[8] -> BitVec[4]] is turned into [ARR([("BitVec",1)],("BitVec",1),[CONST(4)],[EQ(DVAR(0,0),CONST(8))])]. See also {!Types.sig_decl} for further details. *)
val fun_sort_list_to_sig : (sort_name * index_values) list -> sig_decl

(** Appends a boolean sort to a list of sorts. *)
val append_bool : return_type list -> return_type list

(** Does a lookup on the function declarations to see if there is a match. Parameters: {ol {li the {!Types.return_type} of the function to be matched, i.e. the function name and its index values;} {li the list of its domain sorts.}} Returns the codomain sort by evaluating its indices accordingly with the rules given by the matching function declaration, or raises TypeMismatch if no match is found. *)
val match_fun_sorts : return_type -> (sort_name * index_values) list -> sort_name * index_values

(** Declares a new variable (of a given sort) in this scope. *)
val declare_var : symbol_name -> (sort_name * index_values) -> unit

(** Pushes the variable scope stack. *)
val push_var_scope : unit -> unit

(** Pops the variable scope stack. *)
val pop_var_scope : unit -> unit

(** Gets the sort of an expression, *)
val get_expression_sort : expression -> sort_name * index_values

(** Checks if an expression is a formula. *)
val expression_is_formula : expression -> bool

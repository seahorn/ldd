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

(** Hash tables and other persistent structures used by the parser. *)

open Types

(** {6 Exceptions} *)

(** [ValidationError] exception (raised also by {!Support} and {!Smt_parser}) *)
exception ValidationError of string

(** {6 Functions} *)

(** Variable scope stack. *)
val prev_var_scopes : symbol_name list list ref

(** Variable scope stack. *)
val curr_var_scope : symbol_name list ref

(** Returns the id associated with a symbol name (string), or extracts a new id if the simbol is not found. *)
val get_id_num_from_symbol : string -> id_counter_type

(** Returns the symbol name (string) associated with a {!Types.id_counter_type}. *)
val get_symbol_from_id_num : id_counter_type -> string

(** Keeps track of numerals. Useful for printing purposes in order to distinguish them from constants (e.g., the numeral [bv5 : BitVec[32]] has to be printed as [bv5[32]] instead of [bv5 BitVec[32]]). *)
val mark_numeral_as_indexed : symbol_name -> unit

(** True iff the constant is a numeral. *)
val is_numeral_indexed : symbol_name -> bool

(** Gets the {!Types.sort_name} associated with the ["Int"] sort. *)
val get_int_sort_id : sort_name

(** Gets the {!Types.sort_name} associated with the ["Real"] sort. *)
val get_real_sort_id : sort_name

(** Gets the {!Types.sort_name} associated with the ["Bool"] sort. *)
val bool_sort : sort_name

(** Gets the {!Types.return_type} associated with the ["Bool"] sort. *)
val bool_sort_return_type : sort_name * index_values 

(** Returns the signature declarations from a theory-defined function symbol (see also {!Support.declare_fun}). *)
val get_base_fun_decls : symbol_name -> sig_decl list

(** Returns the signature declarations from a user-defined function symbol (see also {!Support.declare_fun}). *)
val get_extra_fun_decls : symbol_name -> sig_decl list

(** Associates the signature declarations with a theory-defined function symbol (see also {!Support.declare_fun}). *)
val replace_base_fun_decls : symbol_name -> sig_decl list -> unit

(** Associates the signature declarations with a user-defined function symbol (see also {!Support.declare_fun}). *)
val replace_extra_fun_decls : symbol_name -> sig_decl list -> unit

(** Associates a theory-defined sort declaration with a sort name (see also {!Support.declare_base_sort}. *)
val replace_base_sort_decl : sort_name -> sort_decl -> unit

(** Adds the user-defined sort declaration associated with a sort name (see also {!Support.declare_sort}. *)
val add_extra_sort_decl : sort_name -> sort_decl -> unit

(** True iff the parameter is a theory-defined sort. *)
val is_base_sort : sort_name -> bool

(** True iff the parameter is a user-defined sort. *)
val is_extra_sort : sort_name -> bool

(** Gets the sort (including its index values if any) of a variable.  *)
val get_var_sort : symbol_name -> sort_name * index_values

(** Associates a variable with its sort (see also {!Support.declare_var}. *)
val add_var_sort : symbol_name -> (sort_name * index_values) -> unit

(** Removes the association between a variable and its sort (used for handling variable scopes, see also {!Support.pop_var_scope}). *)
val remove_var_sort : symbol_name -> unit

(** Folding on user-defined sorts. (For printing purposes, see {!Printing.string_of_extra_sorts} and {!Xml_printing.xml_string_of_extra_sorts}.) *)
val fold_on_extra_sort : (sort_name -> sort_decl -> string -> string) -> string -> string

(** Folding on user-defined function declarations. (For printing purposes, see {!Printing.string_of_extra_funs}, {!Printing.string_of_extra_preds}, {!Xml_printing.xml_string_of_extra_funs}, and {!Xml_printing.xml_string_of_extra_preds}.) *)
val fold_on_extra_fun_decls : (symbol_name -> sig_decl list -> string -> string) -> string -> string

(** Adds an attribute that is not uniquely defined (i.e., benchmark annotations) to the benchmark. *)
val add_bench_attribute : annotation -> unit

(** Adds an attribute that is uniquely defined (i.e., status or logic) to the benchmark. Raises a {!ValidationError} if the attribute is already defined. *)
val add_unique_bench_attribute : string * string option -> unit

(** Adds an assumption to the benchmark. *)
val add_bench_assumption : expression -> unit

(** Test if an attribute is already defined. *) 
val bench_attribute_exists : string -> bool

(** Adds a formula to the benchmark. Raises a {!ValidationError} if the formula is already defined. *)
val set_bench_formula : expression -> unit

(** Gets the current formula from the benchmark. Raises a {!ValidationError} if no formula is defined. *)
val get_bench_formula : unit -> expression

(** Returns the benchmark attributes such as logic, status, annotations.... (For printing purposes, see {!Printing.print_bench} and {!Xml_printing.print_bench}). *)
val get_bench_attributes : unit -> annotation list

(** Returns the benchmark assumptions. (For printing purposes only (see {!Printing.print_bench} and {!Xml_printing.print_bench}).) *)
val get_bench_assumptions : unit -> expression list

(** Replaces a benchmark attribute (see {!Xmltransbench.parse_benchmark}). *)
val replace_bench_attribute : string -> string option -> unit

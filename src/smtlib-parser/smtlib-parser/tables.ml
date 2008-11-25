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

(** Hash tables and other persistent structures used by the parser, along with a few general supporting manipulations functions. *)

open Types

(** [ValidationError] exception (raised also by {!Support} and {!Smt_parser}) *)
exception ValidationError of string

(*****************************************************************************)
(* tables *)

(** Matching symbol strings to ints, extend length to avoid compare problems. *)
(* identifier & symbol tables *)
module LongStringHash =
  Hashtbl.Make (
    struct
      type t = string
      let equal x y = ((compare (x:string) (y:string)) = 0)
      let hash x = Hashtbl.hash_param 200 200 (x:string)
    end
  )

(** Symbol table. *)
let sym_truenaming_table = (LongStringHash.create 1:(int)LongStringHash.t)

(** Symbols to ids table. *)
let id_to_sym_name_hash = (Hashtbl.create 1:(id_counter_type,string)Hashtbl.t)

(** Theory-defined sorts. *)
let id_to_base_sort_hash = (Hashtbl.create 1:(symbol_name,sort_decl)Hashtbl.t)

(** User-defined sorts. *)
let id_to_extra_sort_hash = (Hashtbl.create 1:(symbol_name,sort_decl)Hashtbl.t)

(** Theory-defined functions. *)
let id_to_base_fun_decls_hash = (Hashtbl.create 1:(symbol_name,sig_decl list)Hashtbl.t)

(** User-defined functions. *)
let id_to_extra_fun_decls_hash = (Hashtbl.create 1:(symbol_name,sig_decl list)Hashtbl.t)

(** Variables. *)
let id_to_var_sorts_hash = (Hashtbl.create 1:(symbol_name,return_type)Hashtbl.t)

(** Variable scope stack. *)
let prev_var_scopes = ref [([]:Types.symbol_name list)]

(** Variable scope stack. *)
let curr_var_scope = ref ([]:Types.symbol_name list)

(** Benchmark attributes. *)
let bench_attributes_list = ref ([]:annotation list)

(** Benchmark assumptions. *)
let bench_assumptions_list = ref ([]:expression list)

(** Benchmark formula. *)
let bench_formula = ref (None:expression option)

(** Indexed numerals. *)
(* Keeps track of any numeral that requires an index for printout *)
(* Get actual value from AST's return_type *)
let indexed_numerals = (Hashtbl.create 1:(symbol_name,bool)Hashtbl.t)

(*****************************************************************************)
 
(*****************************************************************************)
(* identifer & symbol functions *)

(** Counter for ids *)
let id_counter = ref 0

(** Gets a new id *)
let get_new_id_num () =
  incr id_counter;
  !id_counter

(** Returns the id associated with a symbol name (string), or extracts a new id if the simbol is not found. *)
let get_id_num_from_symbol sym =
  try
    LongStringHash.find sym_truenaming_table sym
  with Not_found ->
    let id = get_new_id_num() in
    LongStringHash.add sym_truenaming_table sym id;
    Hashtbl.add id_to_sym_name_hash id sym;
    id

(** Returns the symbol name (string) associated with a {!Types.id_counter_type}. *)
let get_symbol_from_id_num = Hashtbl.find id_to_sym_name_hash

(** Keeps track of numerals. Useful for printing purposes in order to distinguish them from constants (e.g., the numeral [bv5 : BitVec[32]] has to be printed as [bv5[32]] instead of [bv5 BitVec[32]]). *)
let mark_numeral_as_indexed x = Hashtbl.add indexed_numerals x true

(** True iff the constant is a numeral. *)
let is_numeral_indexed x = Hashtbl.mem indexed_numerals x

(*****************************************************************************)
(* table access *)
(*****************************************************************************)
(*****************************************************************************)
(* basic sorts *)
(** Gets the {!Types.sort_name} associated with the ["Int"] sort. *)
let get_int_sort_id =
  SYM_ID(get_id_num_from_symbol "Int",0)

(** Gets the {!Types.sort_name} associated with the ["Real"] sort. *)
let get_real_sort_id =
  SYM_ID(get_id_num_from_symbol "Real",0)

(** Gets the {!Types.sort_name} associated with the ["Bool"] sort. *)
let get_bool_sort_id =
  SYM_ID(get_id_num_from_symbol "Bool",0)

(** Gets the {!Types.return_type} associated with the ["Bool"] sort. *)
let bool_sort = get_bool_sort_id

(** Returns the signature declarations from a theory-defined function symbol (see also {!Support.declare_fun}). *)
let bool_sort_return_type = (get_bool_sort_id,([]:index_values))

(** Returns the signature declarations from a theory-defined function symbol (see also {!Support.declare_fun}). *)
let get_base_fun_decls id = Hashtbl.find id_to_base_fun_decls_hash id

(** Returns the signature declarations from a user-defined function symbol (see also {!Support.declare_fun}). *)
let get_extra_fun_decls id = Hashtbl.find id_to_extra_fun_decls_hash id

(** Associates the signature declarations with a theory-defined function symbol (see also {!Support.declare_fun}). *)
let replace_base_fun_decls id sigs = Hashtbl.replace id_to_base_fun_decls_hash id sigs

(** Associates the signature declarations with a user-defined function symbol (see also {!Support.declare_fun}). *)
let replace_extra_fun_decls id sigs = Hashtbl.replace id_to_extra_fun_decls_hash id sigs

(** Associates a theory-defined sort declaration with a sort name (see also {!Support.declare_base_sort}. *)
let replace_base_sort_decl id sort = Hashtbl.replace id_to_base_sort_hash id sort

(** Adds the user-defined sort declaration associated with a sort name (see also {!Support.declare_sort}. *)
let add_extra_sort_decl id sort = Hashtbl.add id_to_extra_sort_hash id sort

(** True iff the parameter is a theory-defined sort. *)
let is_base_sort id = Hashtbl.mem id_to_base_sort_hash id

(** True iff the parameter is a user-defined sort. *)
let is_extra_sort id = Hashtbl.mem id_to_extra_sort_hash id

(** Gets the sort (including its index values if any) of a variable.  *)
let get_var_sort id = Hashtbl.find id_to_var_sorts_hash id

(** Associates a variable with its sort (see also {!Support.declare_var}. *)
let add_var_sort id rtype = Hashtbl.add id_to_var_sorts_hash id rtype

(** Removes the association between a variable and its sort (used for handling variable scopes, see also {!Support.pop_var_scope}). *)
let remove_var_sort id = Hashtbl.remove id_to_var_sorts_hash id

(** Folding on user-defined sorts. (For printing purposes, see {!Printing.string_of_extra_sorts} and {!Xml_printing.xml_string_of_extra_sorts}.) *)
let fold_on_extra_sort f x = Hashtbl.fold f id_to_extra_sort_hash x

(** Folding on user-defined function declarations. (For printing purposes, see {!Printing.string_of_extra_funs}, {!Printing.string_of_extra_preds}, {!Xml_printing.xml_string_of_extra_funs}, and {!Xml_printing.xml_string_of_extra_preds}.) *)
let fold_on_extra_fun_decls f x = Hashtbl.fold f id_to_extra_fun_decls_hash x


(*****************************************************************************)
(* benchmark attributes *)

(** Adds an attribute that is not uniquely defined (i.e., benchmark annotations) to the benchmark. *)
let add_bench_attribute a =
  bench_attributes_list := a::(!bench_attributes_list)

(** Adds an attribute that is uniquely defined (i.e., status or logic) to the benchmark. Raises a {!ValidationError} if the attribute is already defined. *)
let add_unique_bench_attribute (al,at) =
  if List.mem_assoc al !bench_attributes_list then
    raise (ValidationError (al^" defined multiple times."))
  else
    bench_attributes_list := (al,at)::(!bench_attributes_list)

(** Adds an assumption to the benchmark. *)
let add_bench_assumption f =
  bench_assumptions_list := f::(!bench_assumptions_list)

(** Test if an attribute is already defined. *) 
let bench_attribute_exists key =
  List.mem_assoc key !bench_attributes_list

(** Replaces a benchmark attribute (see {!Xmltransbench.parse_benchmark}). *)
let replace_bench_attribute k s =
  bench_attributes_list := List.remove_assoc k !bench_attributes_list;
  add_bench_attribute (k,s)

(** Returns the benchmark attributes such as logic, status, annotations.... (For printing purposes, see {!Printing.print_bench} and {!Xml_printing.print_bench}). *)
let get_bench_attributes () =
  List.rev (!bench_attributes_list)

(** Returns the benchmark assumptions. (For printing purposes only (see {!Printing.print_bench} and {!Xml_printing.print_bench}).) *)
let get_bench_assumptions () =
  List.rev (!bench_assumptions_list)

(** Adds a formula to the benchmark. Raises a {!ValidationError} if the formula is already defined. *)
let set_bench_formula f = 
  match !bench_formula with 
      None -> bench_formula := Some f
    | Some _ -> raise (ValidationError "Formula defined multiple times.")

(** Gets the current formula from the benchmark. Raises a {!ValidationError} if no formula is defined. *)
let get_bench_formula () =
  match !bench_formula with
      None -> raise (ValidationError "No formula defined.")
    | Some x -> x


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

(** Routines for the conversion of the logic definitions (see, e.g., {!Logic_smt} and all the other [Logic_*] modules) into their internal representation. *)

open Types

(* Open the logics *)
open Logic_smt
open Logic_auflia
open Logic_auflira
open Logic_aufnira
open Logic_qf_a
open Logic_qf_aufbv
open Logic_qf_auflia
open Logic_qf_ax
open Logic_qf_bv
open Logic_qf_idl
open Logic_qf_lia
open Logic_qf_lra
open Logic_qf_rdl
open Logic_qf_ufbv32
open Logic_qf_ufbv
open Logic_qf_ufidl
open Logic_qf_uflia
open Logic_qf_uflra
open Logic_qf_uf

open Tables
open Support

(** {6 Exceptions} *)

(** Raised by {!load_logic} when trying to load a logic whose name is not contained in {!assoc_logic_list}. *)
exception LogicSyntaxErr of string

(***************************************************************)
(* converting from logic datatypes to internal ast *)

(** {6 Functions} *)

(** Converts a {!Types.sym_type} (see, e.g., the {!Logic_smt} module) into its corresponding {!Types.symbol_name}. *)
(* sym_type -> symbol_name *)
let convert_logic_id i =
  match i with
    Sym(s) -> SYM_ID((get_id_num_from_symbol s),0)
  | ISym(s,n) -> SYM_ID((get_id_num_from_symbol s), n)

(** Converts a {!Types.sort_type} (see, e.g., the {!Logic_smt} module) into its corresponding {!Types.symbol_name}. *)
(* sort_type -> sort_name *)
let convert_logic_sort i =
  match i with
    Sort(s) -> SYM_ID(get_id_num_from_symbol s,0)
  | ISort(s,n) -> SYM_ID(get_id_num_from_symbol s, n)

(** Converts a {!Types.typed_symbol} (see, e.g., the {!Logic_smt} module) into its corresponding pair [({!Types.symbol_name} * {!Types.sig_decl})]. *)
(* typed_symbol -> symbol_name * sig_decl *)
let rec convert_logic_fun f =
  match f with
    | ExFun(n,s1,s2) ->(convert_logic_id n),EXARR(convert_logic_sort s1, convert_logic_sort s2)
    | Fun(n,ls,r) ->(convert_logic_id n),ARR((List.map (fun x -> convert_logic_sort x) ls),convert_logic_sort r,[],[])
    | CFun(n,ls,r,tl,cl) ->(convert_logic_id n),ARR((List.map (fun x -> convert_logic_sort x) ls),convert_logic_sort r,tl,cl)


(***************************************************************)
(* loading logic signatures *)

(** The associative list contains all logic objects along with their names. Modify this if you add or remove logics. *)
let assoc_logic_list = [
  ("AUFLIA", new logic_AUFLIA);
  ("AUFLIRA", new logic_AUFLIRA);
  ("AUFNIRA", new logic_AUFNIRA);
  ("QF_A", new logic_QF_A);
  ("QF_AUFBV", new logic_QF_AUFBV);
  ("QF_AUFLIA", new logic_QF_AUFLIA);
  ("QF_AX", new logic_QF_AX);
  ("QF_BV", new logic_QF_BV);
  ("QF_IDL", new logic_QF_IDL);
  ("QF_LIA", new logic_QF_LIA);
  ("QF_LRA", new logic_QF_LRA);
  ("QF_RDL", new logic_QF_RDL);
  ("QF_UF", new logic_QF_UF);
  ("QF_UFBV", new logic_QF_UFBV);
  ("QF_UFBV[32]", new logic_QF_UFBV32);
  ("QF_UFIDL", new logic_QF_UFIDL);
  ("QF_UFLIA", new logic_QF_UFLIA);
  ("QF_UFLRA", new logic_QF_UFLRA)
]

(** Converts a logic into its corresponding internal AST. *)
(* string -> unit *)
let load_logic_signature logic =
  List.iter (fun x ->
    declare_base_sort (convert_logic_sort x)) (logic :> logic_smt)#get_theory_sorts;
  List.iter (fun x ->
    declare_base_fun (convert_logic_fun x)) (logic :> logic_smt)#get_theory_funs;
  let ns,np = (logic :> logic_smt)#get_numeral_sort in
  numeral_sort := (convert_logic_sort ns);
  numeral_sort_indices := np

(** Converts a logic into its corresponding internal AST. *)
(* string -> unit *)
let load_logic logic_name =
  try
    let s = String.uppercase logic_name in
    load_logic_signature (List.assoc s assoc_logic_list)
  with Not_found -> raise (LogicSyntaxErr ("Unknown logic "^logic_name))

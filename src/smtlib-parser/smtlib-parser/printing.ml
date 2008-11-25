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

(** Printout-related routines. *)

open Types
open Tables
open Eval

(** {6 Exceptions} *)

(** [PrintingError] exception (raised also by {!Xml_printing}). *)
exception PrintingError

(**************************************************************************)

(** {6 Functions} *)

(** True iff the parameter is a boolean function (i.e., a predicate). *)
(* sort_id -> bool *)
let rec is_predicate s = 
  match s with
      ARR(_,x,_,_) -> x=bool_sort
    | EXARR(_,x) -> x=bool_sort
    | ANNOTATED_ARR(x,_) -> is_predicate x

(** Gets the codomain sort of an expression or term. *)
(* expression -> return_type *)
let get_expression_sort exp =
    match exp with
        EX (_,r) -> r
      | EXA (_,r,_) -> r

(** True iff the expression is a formula. *)
(* expression -> bool *)
let expression_is_formula ex =
  (get_expression_sort ex)=bool_sort_return_type


(**************************************************************************)

(** Prints out a list of indices. *)
(* index_values -> string *)
let rec string_of_index_values ls =
  match ls with
      [x] -> string_of_int x
    | h::t -> (string_of_int h)^":"^(string_of_index_values t)
    | [] -> ""

(** Prints out a symbol name. *)
(* symbol_name -> string *)
let string_of_symbol_name (SYM_ID(x,_)) =
  get_symbol_from_id_num x


(** Prints out a return type. *)
(* return_type -> string *)
let string_of_return_type (SYM_ID(x,_),y) =
  if List.length y > 0 then
    (get_symbol_from_id_num x)^"["^(string_of_index_values y)^"]"
  else
    (get_symbol_from_id_num x)

(** Prints out an annotation. *)
(* annotation -> string *)
let string_of_annotation (a,ao) =
  a^(
    match ao with
        None -> ""
      | Some x -> " "^x)

(** Prints out a list of annotations. *)
(* annotation list -> string *)
let rec string_of_annotation_list al =
  match al with
      [] -> ""
    | [x] -> string_of_annotation x
    | h::t -> (string_of_annotation h)^" "^(string_of_annotation_list t)

(** Prints out a sort name. *)
(* sort_name -> string *)
let string_of_sort = string_of_symbol_name

(** Prints out a (possibly annotated) sort declaration. *)
(* sort_decl -> string *)
let rec string_of_sort_decl s =
  match s with
     SORT x -> string_of_sort x
   | ANNOTATED_SORT (x,a) -> (string_of_sort x)^" "^(string_of_annotation_list a)


(** Prints out a (possibly annotated) user-defined function declaration. See also {!Support.fun_sort_list_to_sig} for further details on how user-defined functions/predicates are intenally represented. *)
(* sig_decl -> string *)
let rec string_of_extra_fun_sig s =
  match s with
      ARR (xs,r,tl,cl) -> 
        let num_params = List.length xs in                                    (* get the arity of the function *)
        let param_indices = get_index_values_for_parameters num_params cl in  (* get the index values of the domain sorts from the constraints *)
        let return_indices = get_index_values_for_output tl in                (* get the index values of the codomain sort from the terms *)
        let param_vals = List.map2 (fun x y -> (x,y)) xs param_indices in     (* build the return types for the domain sorts... *)
        let return_val = (r,return_indices) in                                (* ...and for the codomain sort. *)
        (List.fold_left (fun acc x -> acc^" "^(string_of_return_type x)) "" param_vals) ^ " " ^ (string_of_return_type return_val)
    | EXARR (_,_) -> raise PrintingError                                      (* user-defined functions cannot be extensible. *)
    | ANNOTATED_ARR (s,a) -> (string_of_extra_fun_sig s)^" "^(string_of_annotation_list a)

(** Prints out a (possibly annotated) user-defined function declaration. See also {!Support.fun_sort_list_to_sig} for further details on how user-defined functions/predicates are intenally represented. *)
(* sig_decl -> string *)
let rec string_of_extra_pred_sig s =
  match s with
      ARR (xs,r,tl,cl) -> 
        let num_params = List.length xs in                                    (* get the arity of the predicate *)
        let param_indices = get_index_values_for_parameters num_params cl in  (* get the index values of the domain sorts from the constraints *)
        let param_vals = List.map2 (fun x y -> (x,y)) xs param_indices in     (* build the return types for the domain sorts. *)
        (List.fold_left (fun acc x -> acc^" "^(string_of_return_type x)) "" param_vals)
    | EXARR (_,_) -> raise PrintingError                                      (* user-defined predicates cannot be extensible *)
    | ANNOTATED_ARR (s,a) -> (string_of_extra_pred_sig s)^" "^(string_of_annotation_list a)

(** Prints out a quantifier. *)
(* quant -> string *)
let string_of_quant q = 
  match q with
    | FORALL -> "forall"
    | EXISTS -> "exists"

(** Prints out an expression. *)
(* expression -> string *)
let rec string_of_expression e =
  begin
    match e with
        EX(e1,ret) -> (string_of_term e1 ret)
      | EXA(e1,ret,a) -> "("^(string_of_term e1 ret)^" "^(string_of_annotation_list a)^")"
  end
(** Prints out a term. *)
(* term -> string *)
and string_of_term e ret = 
  begin
    match e with
        VAR tid -> string_of_symbol_name tid
      | FUN (tid,pvals,[]) -> (string_of_return_type (tid,pvals))^(
          if is_numeral_indexed tid then
            begin
              let (_,il) = ret in
              "["^(string_of_index_values il)^"]"
            end
          else ""
        )
      | FUN (tid,pvals,e) -> "("^(string_of_return_type (tid,pvals))^
          (List.fold_left (fun acc x -> acc^" "^(string_of_expression x)) "" e)
           ^")"
      | LET (f,e1,e2) ->"("^
          (if expression_is_formula e1 then "flet" else "let")^
          "("^(string_of_symbol_name f)^" "^(string_of_expression e1)^")"^
          (string_of_expression e2)^")"
      | QUANT (q,b,e1) -> "("^(string_of_quant q)^
          "("^(List.fold_left (fun acc (bv,bs) -> acc^" "^(string_of_symbol_name bv)^":"^(string_of_return_type bs)) "" b)^")"
          ^(string_of_expression e1)^")"
  end

(** Prints out all the user-defined sorts. *)
(* unit -> string *)
let string_of_extra_sorts () =
    fold_on_extra_sort (fun x _ acc -> acc^":extrasorts (("^(string_of_symbol_name x)^"))\n") ""

(** Prints out all the user-defined functions. *)
(* unit -> string *)
let string_of_extra_funs () = 
  fold_on_extra_fun_decls (fun x ls acc -> 
    acc^(List.fold_left (fun acc2 s ->
      if is_predicate s then
        acc2
      else
        acc2^":extrafuns (("^(string_of_symbol_name x)^(string_of_extra_fun_sig s)^"))\n"
    ) "" ls)
  ) ""

(** Prints out all the user-defined predicates. *)
(* unit -> string *)
let string_of_extra_preds () = 
  fold_on_extra_fun_decls (fun x ls acc -> 
    acc^(List.fold_left (fun acc2 s ->
      if is_predicate s then
        acc2^":extrapreds (("^(string_of_symbol_name x)^(string_of_extra_pred_sig s)^"))\n"
      else
        acc2
    ) "" ls)
  ) ""

(** Prints out the whole benchmark. *)
(* benchmark -> unit *)
let print_bench (BENCH (name,attrs)) =
  Printf.printf "(benchmark %s\n" name;
  List.iter (fun (a1,a2) ->
    let s = match a2 with
        None -> ""
      | Some x -> " "^x
    in
    Printf.printf ":%s%s\n" a1 s
  ) (get_bench_attributes ());
  Printf.printf "%s" (string_of_extra_sorts());
  Printf.printf "%s" (string_of_extra_preds());
  Printf.printf "%s" (string_of_extra_funs());
  List.iter (fun x -> Printf.printf ":assumption %s\n" (string_of_expression x)) (get_bench_assumptions ());
  Printf.printf ":formula %s\n" (string_of_expression (get_bench_formula ()));
  Printf.printf ")\n";


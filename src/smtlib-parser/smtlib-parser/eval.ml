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

(** Terms (see {!Types.isort_term}) and constraints (see {!Types.isort_constr}) evaluation routines *)

open Types

(** {6 Exceptions} *)

(** Indices out of bound. *)
exception List_too_short of string 

(** The signature declaration is not associated to a user-defined one. *)
exception Sig_decl_not_extrafun 

(** {6 Functions} *)

(** Extracts the index values list from a list of return types. *)
let extract_indices parameter_sorts =
  List.rev (List.fold_left (fun arr (_,x) -> x::arr) [] parameter_sorts)

(*** Term/Constraint evaluation ***)

(** Term evaluation. It takes in input the term to be evaluated, the index values of the function and the list of index values of the domain sorts. *)
(* isort_term -> index_values -> index_values list -> int *)
let rec term_eval term func dom =
 match term with
   Const(x) -> x
 | Dvar(x,y) ->
   begin
     try
       List.nth (List.nth dom x) y
     with _ -> 
       raise (List_too_short ("The element Dvar("^(string_of_int x)^","^(string_of_int y)^") does not exist in the list of actual indices\n"))
   end
 | Fvar(x) ->  
   begin
     try
       List.nth func x
     with _ ->
       raise (List_too_short ("The element Fvar("^(string_of_int x)^") does not exist in the list of actual indices\n"))
   end
 | Uminus(x) -> - ( term_eval x func dom )
 | Plus(x,y) -> ( term_eval x func dom ) + ( term_eval y func dom )
 | Minus(x,y) -> ( term_eval x func dom ) - ( term_eval y func dom )
 | Times(x,y) -> ( term_eval x func dom ) * ( term_eval y func dom )
 | Div(x,y) -> ( term_eval x func dom ) / ( term_eval y func dom )

(** Constraint evaluation. It takes in input the term to be evaluated, the index values of the function and the list of index values of the domain sorts. *)
(* isort_constr -> index_values -> index_values list -> bool *)
let rec constr_eval constr func dom =
 match constr with
    Eq(x,y) -> ( term_eval x func dom ) = ( term_eval y func dom )
  | Lt(x,y) -> ( term_eval x func dom ) < ( term_eval y func dom )
  | Leq(x,y) -> ( term_eval x func dom ) <= ( term_eval y func dom )
  | Gt(x,y) -> ( term_eval x func dom ) > ( term_eval y func dom )
  | Geq(x,y) -> ( term_eval x func dom ) >= ( term_eval y func dom )
  | Not(x) -> not (constr_eval x func dom )
  | And(x,y) -> (constr_eval x func dom ) && (constr_eval y func dom )
  | Or(x,y) -> (constr_eval x func dom ) || (constr_eval y func dom )
  | Implies(x,y) -> if (constr_eval x func dom ) then (constr_eval y func dom ) else true
  | Iff(x,y) -> ((constr_eval x func dom ) && (constr_eval y func dom )) || (not (constr_eval x func dom ) && not (constr_eval y func dom ))

(*** Term/constraint generation ***)

(** Term generation. From the index values of the codomain sort, it generates the term list of the signature declaration (see {!Types.sig_decl}) associated to user-defined functions. *)
(* index_values -> isort_term list *)
let indices2terms x =
   List.map (fun x -> Const(x)) x

(** Constraint generation. From the index values of the n-th domain sort, it generates the constraint list of the signature declaration (see {!Types.sig_decl}) associated to user-defined function. Called by {!Eval.indicesl2constrs}. *)
(* int -> index_values -> isort_constr list *)
let indices2constrs x y =
   let l = Array.to_list (Array.init (List.length y) (fun x -> x)) in
   List.map2 (fun a b -> Eq(Dvar(x,a),Const(b))) l y

(** Constraint generation. From the list of index values of the domain sorts, it generates the constraint list of the signature declaration (see {!Types.sig_decl}) associated to user-defined functions. *)
(* index_values list -> isort_constr list *)
let indicesl2constrs y =
   let l = Array.to_list (Array.init (List.length y) (fun x -> x)) in
   List.concat (List.map2 indices2constrs l y)


(*** Printing related routines ***)

(** (For printing purposes.) Gets the index values of the codomain sort from a signature declaration (see {!Types.sig_decl}) associated to a user-defined function (it returns an empty list if none). Called by {!Printing.string_of_extra_fun_sig}. *)
(* isort_term list -> index_values *)
let get_index_values_for_output tl =
  List.map (fun x ->
    match x with
      Const(x) -> x
    | _ -> raise Sig_decl_not_extrafun) tl

(** (For printing purposes.) Gets the list of index values of the domain sorts from a signature declaration (see {!Types.sig_decl}) associated to a user-defined function. Called by {!Printing.string_of_extra_fun_sig} and {!Printing.string_of_extra_pred_sig}. *)
(* int -> isort_constr list -> index_values list *)
let get_index_values_for_parameters num_params cl =
  let arr = Array.mapi (fun i _ ->
    List.rev (List.fold_left (fun acc x -> 
               match x with
                 Eq(Dvar(a,b),Const(c)) -> if a=i then
                                             c::acc
                                           else
                                             acc
                 | _ -> acc
            ) [] cl)
    ) (Array.make num_params 0)
  in
  Array.to_list arr


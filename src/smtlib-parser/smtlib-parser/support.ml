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
open Eval
open Tables
open Printing

(** {6 Exceptions} *)

(** [TypeMismatch] exception (raised also by {!Smt_parser}). *)
exception TypeMismatch of string

(** Variable scope stack popped when empty. *)
exception VarScopeErr

(** A sort is declared twice. *)
exception SortRedeclaration of string

(** The empty list of return types is not allowed (see {!fun_sort_list_to_sig}). *)
exception MatchParamErr

(*****************************************************************************)
(** {6 Functions} *)

(*****************************************************************************)
(* base sorts *)

(** True iff s is the boolean sort. *)
(* return_type -> bool *)
let is_predicate_sort s =
  s=bool_sort_return_type

(** Default sort name for numerals. Set by {!Signature.load_logic_signature}. *)
(* symbol_name ref *)
let numeral_sort = ref (get_int_sort_id)

(** Default indices for the numeral sort. Set by {!Signature.load_logic_signature}. *)
(* index_values ref *)
let numeral_sort_indices = ref ([]:index_values)

(** If given an empty list, it returns the default numeral sort (indices included); otherwise, it returns the actual parameter in the place of the default index values. *)
(* index_values -> sort_name * index_values *)
let get_numeral_sort pvals = 
  let parameters = 
    if List.length (pvals) = 0 then
      !numeral_sort_indices
    else
      pvals
  in
  !numeral_sort,parameters

(** Strip function declarations from an annotated function declaration. *)
(* sig_decl -> sig_decl *)
let strip_fun_declarations f =
  match f with
    ANNOTATED_ARR(x,_) -> x
  | x -> x

(** Gets the list of the theory-defined function declarations associated with a symbol. *)
(* symbol_name -> sig_decl list *)
let get_base_fun_declarations id = 
  try
    List.map (strip_fun_declarations) (get_base_fun_decls id)
  with Not_found -> []

(** Gets the list of the user-defined function declarations associated with a symbol. *)
(* symbol_name -> sig_decl list *)
let get_extra_fun_declarations id = 
  try
    List.map (strip_fun_declarations) (get_extra_fun_decls id)
  with Not_found -> []

(** Returns the list of all the signature declarations associated with a symbol. *)
(* symbol_name -> sig_decl list *)
let get_fun_declarations id = 
  let l1 = get_base_fun_declarations id in
  let l2 = get_extra_fun_declarations id in
  List.rev_append l1 l2

(** Given an integer n, it returns the {!Types.isort_term} [list] [[Dvar(1,0);Dvar(1,2);...;Dvar(1,n)]]. Called by {!declare_eq_distinct} in the context of the ["ite"] function declarations. *)
(* int -> isort_term list *)
let generate_ite_terms n =
   let l = Array.to_list (Array.init n (fun x -> x)) in
   List.map (fun a -> Dvar(1,a)) l

(** Given an integer n, it returns the {!Types.isort_constr} [list] [[Eq(Dvar(1,0),Dvar(2,0);Eq(Dvar(1,1),Dvar(2,1);...;Eq(Dvar(1,n),Dvar(2,n))]]. Called by {!declare_eq_distinct} in the context of the ["ite"] function declarations. *)
(* int -> isort_constr list *)
let generate_ite_constraints n =
   let l = Array.to_list (Array.init n (fun x -> x)) in
   List.map (fun a -> Eq(Dvar(1,a),Dvar(2,a))) l

(** Declares "=", "distinct", and "ite" for a given sort. *)
(* sort_name -> unit *)
let declare_eq_distinct (SYM_ID(n1,n2) as paramsort) =
  let eqid = SYM_ID(get_id_num_from_symbol "=",0) in
  let disid = SYM_ID(get_id_num_from_symbol "distinct",0) in
  let iteid = 
    if paramsort=bool_sort then
      SYM_ID(get_id_num_from_symbol "if_then_else",0)
    else
      SYM_ID(get_id_num_from_symbol "ite",0)
  in
  let eq_sig = EXARR (paramsort,bool_sort) in
  let ite_sig = ARR([bool_sort;paramsort;paramsort],paramsort,(generate_ite_terms n2),(generate_ite_constraints n2)) in

  let eq_sigs = get_fun_declarations eqid in
  let dis_sigs = get_fun_declarations disid in
  let ite_sigs = get_fun_declarations iteid in
  replace_base_fun_decls eqid (eq_sig::eq_sigs);
  replace_base_fun_decls disid (eq_sig::dis_sigs);
  replace_base_fun_decls iteid (ite_sig::ite_sigs)

(*****************************************************************************)
(* sort functions *)

(** Declares a theory-defined sort. *)
(* sort_name -> unit *)
let declare_base_sort id =
  let sort = (SORT(id)) in
  replace_base_sort_decl id sort;
  declare_eq_distinct id

(** Declares a user-defined sort. Raises a {!SortRedeclaration} exception if the sort is already declared (either theory- or  user-defined). *)
(* sort_name -> unit *)
let declare_sort id =
  let sort = (SORT(id)) in
  if is_base_sort id || is_extra_sort id then
    raise (SortRedeclaration (string_of_symbol_name id));
  add_extra_sort_decl id sort;
  declare_eq_distinct id

(** Checks if a given user-defined function declaration matches with a theory-defined one. True iff the theory- and the user-defined ones have the same domain sort names (indices excluded). *)
(* sig_decl -> sig_decl -> bool *)
let match_param_sorts_in_base_signatures sig1 sig2 =
  match (strip_fun_declarations sig1),(strip_fun_declarations sig2) with
  | ARR(x,_,_,_), ARR(y,_,_,_) ->
      if List.length x = List.length y then
        (List.fold_left2 (fun acc w z -> acc && w=z) true x y)
      else
        false
  | EXARR(x,_), EXARR(y,_) -> 
      x=y
  | ARR(x,_,_,_), EXARR(y,_) -> 
      List.fold_left (fun acc z -> acc && z=y) true x
  | EXARR(y,_), ARR(x,_,_,_) -> 
      List.fold_left (fun acc z -> acc && z=y) true x
  | _,_ -> false

(** Checks if a given user-defined function declaration matches with another user-defined one. True iff both the declarations have the same domain sorts (indices included). *)
(* sig_decl -> sig_decl -> bool *)
let match_param_sorts_in_extend_signatures sig1 sig2 =
  match (strip_fun_declarations sig1),(strip_fun_declarations sig2) with
  | ARR(x,_,_,x2), ARR(y,_,_,y2) ->
          (List.length x = List.length y) &&
          (List.length x2 = List.length y2) &&
          (List.fold_left2 (fun acc w z -> acc && w=z) true x y) &&
          (List.fold_left2 (fun acc w z -> acc && w=z) true x2 y2)
  | _,_ -> false

(** Converts a list of pairs [(]{!Types.sort_name}[ * ]{!Types.index_values}[)] into a function declaration. Called by the parser when an "extrafun/extrapred" declaration is found for turning it into the internal AST. For example, the list [[[("BitVec",1),8];[("BitVec",1),4]]] corresponding to the function [f: BitVec[8] -> BitVec[4]] is turned into [ARR([("BitVec",1)],("BitVec",1),[CONST(4)],[Eq(Dvar(0,0),CONST(8))])]. See also {!Types.sig_decl} for further details. *)
(* (sort_name * index_values) list -> sig_decl *)
let fun_sort_list_to_sig ls =
  match ls with
    (* A constant, where x is the codomain sort *)
    [x] -> let sid,pvals = x in
           let out_terms = indices2terms pvals in (* generate an isort_term list from the index_values *)
           ARR([],sid,out_terms,[])
    (* MatchParamErr: an empty list is not allowed. *)
  | [] -> raise MatchParamErr
    (* A function, where the last element of the list is the codomain sort. *)
  | _ -> let (r,rvals)::rps = List.rev ls in
         let ps = List.rev rps in
         let ps' = List.map (fun (s,_) -> s) ps in
         let domain_pvals = List.map (fun (_,v) -> v) ps in
         let out_terms = indices2terms rvals in             (* generate an isort_term list from the index_values of the codomain sort *)
         let in_constrs = indicesl2constrs domain_pvals in  (* generate an isort_constr list from the index values of the domain sorts *)
         ARR(ps',r,out_terms,in_constrs)

(** Appends a boolean sort to a list of sorts. *)
(* return_type list -> return_type list *)
let append_bool ls =
  match ls with
    [] -> [bool_sort_return_type]
  | _ -> ls @ [bool_sort_return_type]


(*****************************************************************************)
(* function & constant functions *)

(** Determines if a signature already exists (to avoid redeclarations). *)
(* sig_decl -> sig_decl list -> sig_decl list -> bool *)
let check_is_invalid_polymorph sig_type base_signatures extend_signatures =
try
    let base_check =
      (* Check sig_type against theory-defined function declarations. *)
      List.fold_left (fun acc fs ->
        acc || (match_param_sorts_in_base_signatures sig_type fs) 
      ) false base_signatures
    in
      (* Check sig_type against user-defined function declarations. *)
      List.fold_left (fun acc fs -> 
        acc || (match_param_sorts_in_extend_signatures sig_type fs)
      ) base_check extend_signatures
with Not_found -> false

(** Declares a theory-defined function symbol. No sanity checks because a reasoner would be needed to catch ambiguities amongs theory-defined function declarations. *)
(* symbol_name * sig_decl -> unit *)
let declare_base_fun (id,sig_type) =
  let signatures = get_base_fun_declarations id in
(*  if check_is_invalid_polymorph sig_type signatures [] then
    raise (TypeMismatch "Redeclaration of function."); *)
  replace_base_fun_decls id (sig_type::signatures)

(** Declares a user-defined function symbol. Raises {!TypeMismatch} exception if one of the following conditions is satisfied: {ul {li There is a theory-defined function with the same name and the same codomain sort names (index values are excluded from the comparison);} {li A user-defined function (previously defined) has the same name and the same codomain sorts (included their index values).}} *)
(* return_type -> sig_decl -> unit *)
let declare_fun (id,_) sig_type =
  let sigs1 = get_base_fun_declarations id in
  let sigs2 = get_extra_fun_declarations id in
  if check_is_invalid_polymorph sig_type sigs1 sigs2 then
    raise (TypeMismatch "Redeclaration of function.");
  replace_extra_fun_decls id (sig_type::sigs2)

(** Computes the sort of a term obtained by applying a function declared as [decl_f_sig] and indices [pvals] to terms of sort [param_sorts]. Return the appropriate return_type if the function declaration matches with the term sorts, [None] otherwise. *)
(* sig_decl -> index_values -> return_type list -> return_type option *)
let match_params decl_f_sig pvals param_sorts =
  match (strip_fun_declarations decl_f_sig) with
    | EXARR(x,r) ->           (* it is an extensible function *)
        if List.for_all (fun (y,_) -> y=x) param_sorts && (* check if all the term sort names are equal to the name of the domain sort of the function... *)
        List.length param_sorts > 0 &&
        (let (_,z) = List.hd param_sorts in               (* ... and if term sort indices are equal (mandatory for extensible functions). *)
          List.for_all (fun (_,y) -> y=z) param_sorts)
        then
          Some (r,[])
        else
          None
    | ARR (x,r,tl,cl) -> 
        let dom = extract_indices param_sorts in
        if (List.length x = List.length param_sorts) &&         (* The function arity and the number of term sorts are equal. *)
           (List.fold_left2 (fun acc x1 (x2,_) -> acc && x1=x2) (* The term sort names agree with what expected from function declaration. *)
             true x param_sorts) &&
          (List.fold_left (fun acc x -> acc &&                  (* The constraints are satiefied. *)
            (constr_eval x pvals dom)) true cl)
        then
          begin
            let rparam_vals = 
              List.map (fun x -> term_eval x pvals dom) tl      (* Evaluates the isort_term list to compute the index values of the resulting term sort. *)
            in 
            Some (r,rparam_vals)
          end
        else
          None
    | _ -> raise MatchParamErr

(** Does a lookup on the function declarations to see if there is a match. Parameters: {ol {li the {!Types.return_type} of the function to be matched, i.e. the function name and its index values;} {li the list of its domain sorts.}} Returns the codomain sort (evaluating its indices accordingly with the rules given by the matching function declaration), or raises TypeMismatch if no match is found. *)
(* return_type -> (sort_name * index_values) list -> sort_name * index_values *)
let match_fun_sorts ((id,pvals) as f) param_sorts =
  (* Get the list of declarations associated with the symbol. *)
  let potential_sorts = get_fun_declarations id in 
  let fun_sort = 
    List.fold_left (fun acc fs -> 
      if acc = None then
        (* Try to compute the return type of the term resulting by the application of f to terms of sort param_sorts. *)
        match_params fs pvals param_sorts
      else
         acc
    ) None potential_sorts
  in
  match fun_sort with
      None -> raise (TypeMismatch ((Printing.string_of_return_type f)^" ("^
              (List.fold_left 
                (fun acc s -> acc^""^(Printing.string_of_return_type s))
               "" param_sorts)^
              ") does not match a declared signature."))
    | Some x -> x

(*****************************************************************************)
(* functions dealing with variables *)

(** Declares a new variable (of a given sort) in this scope. *)
(* symbol_name -> (sort_name * index_values) -> unit *)
let declare_var id rtype =
  curr_var_scope := id::(!curr_var_scope);
  add_var_sort id rtype

(** Pushes the variable scope stack. *)
(* unit -> unit *)
let push_var_scope () =
  prev_var_scopes := (!curr_var_scope)::(!prev_var_scopes);
  curr_var_scope := []

(** Pops the variable scope stack. *)
(* unit -> unit *)
let pop_var_scope () =
  match !prev_var_scopes with
      [] -> raise VarScopeErr
    | h::t -> 
        List.iter (fun x -> remove_var_sort x) 
          !curr_var_scope;
        curr_var_scope := h;
        prev_var_scopes := t


(*****************************************************************************)
(* expression functions *)

(** Gets the sort of an expression, *)
(* expression -> sort_name * index_values *)
let get_expression_sort exp =
    match exp with 
        EX (_,r) -> r
      | EXA (_,r,_) -> r

(** Checks if an expression is a formula. *)
(* expression -> bool *)
let expression_is_formula ex =
  is_predicate_sort (get_expression_sort ex)


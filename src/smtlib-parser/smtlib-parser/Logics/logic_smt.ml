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

(** Basic logic signature definitions. Each logic should be a class extending this one. Defines all boolean connectives. *)

open Types

let boolean = Sort "Bool"
let integer = Sort "Int"

let substitute s subs =
  if List.mem_assoc s subs then 
    List.assoc s subs
  else
    s
                       
let sub_sorts in_list subs =
  List.map (fun x -> substitute x subs) in_list

(* do not allow redundancies *)
let include_new orig_list new_list =
  List.fold_left (fun acc x -> 
                    if List.mem x orig_list then
                      acc
                    else
                       x::acc
  ) orig_list new_list

(** {6 Classes} *)

(***************************************************************)
class logic_smt =
  object
    val mutable theory_sorts = [boolean]
    val mutable numeral_sort = integer,([]:index_values)
    val mutable theory_funs = [
      Fun(Sym "true",[],boolean);
      Fun(Sym "false",[],boolean);
      Fun(Sym "not",[boolean],boolean);
      Fun(Sym "implies",[boolean;boolean],boolean);
      ExFun(Sym "iff",boolean,boolean);
      ExFun(Sym "and",boolean,boolean);
      ExFun(Sym "xor",boolean,boolean);
      ExFun(Sym "or",boolean,boolean)
      ]
    
    method get_theory_sorts = theory_sorts
    method get_theory_funs = theory_funs
    method get_numeral_sort = numeral_sort
    
    method private import_sorts logic_in subs =
      theory_sorts <- include_new theory_sorts
        (sub_sorts (logic_in :> logic_smt)#get_theory_sorts subs)
      
    method private import_funs logic_in subs =
      theory_funs <- include_new theory_funs
        (List.map (fun x -> match x with
        
                     | Fun(n,ls,r) -> 
                         Fun(n,(sub_sorts ls subs),(substitute r subs))
                     | CFun(n,ls,r,tl,cl) -> 
                         CFun(n,(sub_sorts ls subs),(substitute r subs),tl,cl)
                     | ExFun(n,s1,s2) -> 
                         ExFun(n,substitute s1 subs,substitute s2 subs)
                  ) 
          (logic_in :> logic_smt)#get_theory_funs
        )
end

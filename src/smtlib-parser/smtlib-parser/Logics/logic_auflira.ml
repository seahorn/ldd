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

(** AUFLIRA logic signature definitions. *)
(* Class extending logic_smt.
 *
 * Class methods (defined in an initializer):
 *  - theory_sorts lists all non-Boolean sorts of the logic
 *     This should be appended to the logic_smt values.
 *  - numeral_sort is the type that bare numerals such as "5" are assigned
 *     This also included bitvector numerals.  It also contains a list of 
 *     default indices for these numerals, possibly empty.
 *  - theory_funs are functions, predicates, relations, and constants defined
 *     in the theory.  "=", "distinct", and "ite/if_then_else" are 
 *     automatically defined for all sorts and should not be included here.
 *     This should be appended to the logic_smt values.
*)

open Types

let integer = Sort "Int"
let real = Sort "Real"
let arr = Sort "Array"
let index = Sort "Index"
let elem = Sort "Element"
let arr1 = Sort "Array1"
let arr2 = Sort "Array2"

(** {6 Classes} *)

(***************************************************************)
class logic_AUFLIRA = object (self)
  inherit Logic_smt.logic_smt

  initializer
    let logic1 = new Logic_qf_idl.logic_QF_IDL in
    let logic2 = new Logic_qf_rdl.logic_QF_RDL in
    let logic3 = new Logic_qf_ax.logic_QF_AX in
    numeral_sort <- integer,[];
    self#import_sorts logic1 [];
    self#import_funs logic1 [];
    self#import_sorts logic2 [];
    self#import_funs logic2 [];
    self#import_sorts logic3 [(arr,arr1);(index,integer);(elem,real)];
    self#import_funs logic3 [(arr,arr1);(index,integer);(elem,real)];
    self#import_sorts logic3 [(arr,arr2);(index,integer);(elem,arr1)];
    self#import_funs logic3 [(arr,arr2);(index,integer);(elem,arr1)]
end
 

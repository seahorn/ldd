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

(** QF_AUFBV32 logic signature definitions. *)
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

let zero = Const 0
let one = Const 1

let integer = Sort "Int"
let bv = ISort ("BitVec",1)
let boolean = Sort "Bool"

let m = Dvar(0,0)
let n = Dvar(1,0)

let i = Fvar(0)
let j = Fvar(1)

(** {6 Classes} *)

(***************************************************************)
class logic_QF_UFBV32 = object (self)
  inherit Logic_smt.logic_smt

  initializer
    let logic1 = new Logic_qf_bv.logic_QF_BV in
    numeral_sort <- bv,[32]; 
    self#import_sorts logic1 [];
    self#import_funs logic1 [];
    theory_funs <- List.rev_append theory_funs [
    (* these have some integer parameters, but they are typed as bv32 *)
      CFun(Sym "shift_left0",[bv;bv],bv,[m],[Gt(m,zero)]);
      CFun(Sym "shift_left1",[bv;bv],bv,[m],[Gt(m,zero)]);
      CFun(Sym "shift_right0",[bv;bv],bv,[m],[Gt(m,zero)]);
      CFun(Sym "shift_right1",[bv;bv],bv,[m],[Gt(m,zero)]);
      CFun(Sym "repeat",[bv;bv],bv,[m],[Gt(m,zero)]);
      CFun(Sym "sign_extend",[bv;bv],bv,[m],[Gt(m,zero)]);
      CFun(Sym "rotate_left",[bv;bv],bv,[m],[Gt(m,zero)]);
      CFun(Sym "rotate_right",[bv;bv],bv,[m],[Gt(m,zero)]);
      CFun(ISym ("fill",1),[bv],bv,[i],[Geq(i,zero);Gt(m,zero)])
    ]
end

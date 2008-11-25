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

(** QF_BV logic signature definitions. *)
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

let bv = ISort ("BitVec",1)
let boolean = Sort "Bool"

let m = Dvar(0,0)
let n = Dvar(1,0)

let i = Fvar(0)
let j = Fvar(1)

(** {6 Classes} *)

(***************************************************************)
class logic_QF_BV = object (self)
  inherit Logic_smt.logic_smt

  initializer
  theory_sorts <- List.rev_append theory_sorts [bv];
  numeral_sort <- bv,[];
  theory_funs <- List.rev_append theory_funs [
    CFun(Sym "bit0",[],bv,[one],[]);
    CFun(Sym "bit1",[],bv,[one],[]);
    CFun(Sym "concat",[bv;bv],bv,[Plus(m,n)],[Gt(m,zero);Gt(n,zero)]);
    CFun(ISym ("extract",2),[bv],bv,[Plus(Minus(i,j),one)],[Geq(m,zero);Geq(i,j);Geq(j,zero)]);
    CFun(Sym "bvnot",[bv],bv,[m],[Gt(m,zero)]);
    CFun(Sym "bvneg",[bv],bv,[m],[Gt(m,zero)]);
    CFun(Sym "bvand",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvor",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvadd",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvmul",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvudiv",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvurem",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvshl",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvlshr",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvnor",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvnand",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvxor",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvxnor",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvcomp",[bv;bv],bv,[one],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvsub",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvsdiv",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvsrem",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvsmod",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(Sym "bvashr",[bv;bv],bv,[m],[Gt(m,zero);Eq(m,n)]);
    CFun(ISym ("repeat",1),[bv],bv,[Times(i,m)],[Geq(i,zero);Gt(m,zero)]);
    CFun(ISym ("zero_extend",1),[bv],bv,[Plus(i,m)],[Geq(i,zero);Gt(m,zero)]);
    CFun(ISym ("sign_extend",1),[bv],bv,[Plus(i,m)],[Geq(i,zero);Gt(m,zero)]);
    CFun(ISym ("rotate_left",1),[bv],bv,[m],[Geq(i,zero);Gt(m,zero)]);
    CFun(ISym ("rotate_right",1),[bv],bv,[m],[Geq(i,zero);Gt(m,zero)]);
    CFun(Sym "bvult",[bv;bv],boolean,[],[Gt(m,zero);Eq(n,m)]);
    CFun(Sym "bvule",[bv;bv],boolean,[],[Gt(m,zero);Eq(n,m)]);
    CFun(Sym "bvugt",[bv;bv],boolean,[],[Gt(m,zero);Eq(n,m)]);
    CFun(Sym "bvuge",[bv;bv],boolean,[],[Gt(m,zero);Eq(n,m)]);
    CFun(Sym "bvslt",[bv;bv],boolean,[],[Gt(m,zero);Eq(n,m)]);
    CFun(Sym "bvsle",[bv;bv],boolean,[],[Gt(m,zero);Eq(n,m)]);
    CFun(Sym "bvsgt",[bv;bv],boolean,[],[Gt(m,zero);Eq(n,m)]);
    CFun(Sym "bvsge",[bv;bv],boolean,[],[Gt(m,zero);Eq(n,m)]);
    ]
end

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

(** Definitions of the types used by the parser. *)

(** {6 Types} *)

(** Terms used in signature declarations (both the internal and the human readable ones -- see {!Types.sig_decl} and {!Types.typed_symbol} respectively) for specifying the values of the codomain sort indices. See also the {!Eval} module. *)
type isort_term =
    Const of int                     (** Constant *)
  | Dvar of int * int                (** [Dvar(x,y)] gets the value of the y-th index of the x-th domain sort. *)
  | Fvar of int                      (** [Fvar(x)] gets the value of the x-th function index. *)
  | Uminus of isort_term             (** Unary minus. *)
  | Plus of isort_term * isort_term  (** Sum. *)
  | Minus of isort_term * isort_term (** Difference. *)
  | Times of isort_term * isort_term (** Multiplication. *)
  | Div of isort_term * isort_term   (** (Integer) division. *)

(** Constraints used in signature declarations (both the internal and the human readable ones -- see {!Types.sig_decl} and {!Types.typed_symbol} respectively) for specifying additional constraints over the domain sorts or function indices. See also the {!Eval} module. *)
type isort_constr = 
    Eq of isort_term * isort_term          (** Evaluated to true iff the parameters are evaluated the same. *)
  | Lt of isort_term * isort_term          (** Less. *)
  | Leq of isort_term * isort_term         (** Less or equal. *)
  | Gt of isort_term * isort_term          (** Greater. *)
  | Geq of isort_term * isort_term         (** Greater or equal. *)
  | Not of isort_constr                    (** Logical Not. *)
  | And of isort_constr * isort_constr     (** Logical And. *)
  | Or of isort_constr * isort_constr      (** Logical Or. *)
  | Implies of isort_constr * isort_constr (** Logical Implication. *)
  | Iff of isort_constr * isort_constr     (** Logical If and only if. *)

(** Counters for indexing hashtables (see the {!Tables} module). *)
type id_counter_type = int

(** Semi-human readable function symbol declarations used in {!Logic_smt} and in all the other [Logic_*] modules. *)
type sym_type =
    Sym of string           (* A basic string identifier. *)
  | ISym of string * int    (* An indexed identifier with its number of indices *)

(** Semi-human readable sort declarations used in {!Logic_smt} and in all the other [Logic_*] modules. *)
type sort_type =
    Sort of string          (* Basic string identifier. *)
  | ISort of string * int   (* Indexed identifier with its number of indices *)

(** Semi-human readable declarations for function definitions used in {!Logic_smt} and in all the other [Logic_*] modules. *)
type typed_symbol =
  | Fun of sym_type * sort_type list * sort_type                                              (** Functions without indices. Parameters: {ol {li symbol name;} {li domain sorts;} {li codomain sort.}} *)
  | CFun of sym_type * (sort_type list) * sort_type * (isort_term list) * (isort_constr list) (** Functions with indices. Parameters: {ol {li symbol name;} {li domain sorts;} {li codomain sort;} {li terms for computing the indices associated to the codomain sort;} {li constraints associated to the domain sorts or function indices.}} *)
  | ExFun of sym_type * sort_type * sort_type                                                 (** Extensible functions with one or more parameters over the same sort (indices included). Assumptions: no constraints on domain sort indices and no indices on codomain sort. Parameters: {ol {li symbol name;} {li domain sort;} {li codomain sort.}}*)

(** Annotations. *)
type annotation = string * string option

(** Annotations list. *)
type annotations = annotation list

(** AST identifiers for generic symbols, with its associated number of indices. *)
type symbol_name =
  SYM_ID of id_counter_type * int

(** AST identifiers for sorts. *)
type sort_name = symbol_name

(** Index values (used for indexed function symbols or terms). *)
type index_values = int list

(** Sort of terms: sort/symbol name and index values. *)
type return_type =
  symbol_name * index_values

(** (Internal) sort declarations. *)
type sort_decl = 
    SORT of sort_name                          (** Basic identifier *)
  | ANNOTATED_SORT of sort_name * annotations  (** Annotated indentifier *)

(** (Internal) function symbol declarations. Their associations with symbols are mantained through {!Tables.replace_base_fun_decls} and {!Tables.replace_extra_fun_decls}. *)
type sig_decl =
    ARR of sort_name list * sort_name * (isort_term list) * (isort_constr list) (** Functions. Parameters: {ol {li domain sorts;} {li codomain sort;} {li terms for computing the indices associated to the codomain sort;} {li constraints associated to the domain sorts or function indices.}} *)
  | EXARR of sort_name * sort_name                                              (** Extensible functions (see {!Types.typed_symbol}). *)
  | ANNOTATED_ARR of sig_decl * annotations                                     (** Annotated functions. *)

(** Quantifiers. *)
type quant =
    FORALL 
  | EXISTS

(** Associates a variable to its corresponding sort. *)
type binder = symbol_name * return_type

(** Generic parsed expressions. *)
type expression =
    EX of term * return_type                (** An expression without annotations and its sort. *)
  | EXA of term * return_type * annotations (** An expression with annotations and its sort. *)

(** Parsed terms. *)
and term =
  | VAR of symbol_name                                   (** A variable (bounded or coming from a (f)let expression). *)
  | FUN of symbol_name * index_values * expression list  (** A function with its name, indices, and parameters. *)
  | LET of symbol_name * expression * expression         (** A (f)let expression. *)
  | QUANT of quant * (binder list) * expression          (** A quantified expression with its list of bounded variables. *)

(** Benchmark attributes. *)
type bench_attributes =
    FORMULA of expression
  | ASSUMPTION of expression
  | ATTRIBUTE of annotation

(** A fully parsed benchmark. *)
type benchmark =
  BENCH of string * expression (* The name and the formula. *)
 

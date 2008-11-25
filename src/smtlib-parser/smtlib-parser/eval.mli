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

(** Terms (see {!Types.isort_term}) and constraints (see {!Types.isort_constr}) evaluation routines. *)

open Types

(** {6 Functions} *)

(** Extracts the index values list from a list of return types. *)
val extract_indices : return_type list -> index_values list

(** Term evaluation. It takes in input the term to be evaluated, the index values of the function and the list of index values of the domain sorts. *)
val term_eval : isort_term -> index_values -> index_values list -> int 

(** Constraint evaluation. It takes in input the term to be evaluated, the index values of the function and the list of index values of the domain sorts. *)
val constr_eval : isort_constr -> index_values -> index_values list -> bool

(** Term generation. From the index values of the codomain sort, it generates the term list of the signature declaration (see {!Types.sig_decl}) associated to user-defined functions. *)
val indices2terms : index_values -> isort_term list 

(** Constraint generation. From the list of index values of the domain sorts, it generates the constraint list of the signature declaration (see {!Types.sig_decl}) associated to user-defined functions. *)
val indicesl2constrs : index_values list -> isort_constr list 

(** (For printing purpose.) Gets the index values of the codomain sort from a signature declaration (see {!Types.sig_decl}) associated to a user-defined function. *)
val get_index_values_for_output : isort_term list -> index_values

(** (For printing purpose.) Gets the list of index values of the domain sorts from a signature declaration (see {!Types.sig_decl}) associated to a user-defined function. *)
val get_index_values_for_parameters : int -> isort_constr list -> index_values list

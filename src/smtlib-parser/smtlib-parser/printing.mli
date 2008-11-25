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

(** {6 Exceptions} *)

(** [PrintingError] exception (raised also by {!Xml_printing}). *)
exception PrintingError

(** {6 Functions} *)

(** Prints out a symbol name. *)
val string_of_symbol_name : symbol_name -> string

(** Prints out a return type. *)
val string_of_return_type : return_type -> string

(** Prints out a list of indices. *)
val string_of_index_values : index_values -> string

(** Prints out the whole benchmark. *)
val print_bench : benchmark -> unit

(** True iff the parameter is a boolean function (i.e., a predicate). *)
val is_predicate : sig_decl -> bool

(** True iff the expression is a formula. *)
val expression_is_formula : expression -> bool

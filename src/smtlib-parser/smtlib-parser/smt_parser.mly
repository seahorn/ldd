%{
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

open Types
open Tables
open Support
open Signature

let parse_error msg = print_endline msg

%}
%token <string> BVNUMERAL_TOK
%token <string> BVBINNUMERAL_TOK
%token <string> BVHEXNUMERAL_TOK
%token <string> NUMERAL_TOK
%token <string> RATIONAL_TOK
%token <string> SYM_TOK
%token <string> VAR_TOK
%token <string> FVAR_TOK
%token <string> STRING_TOK
%token <string> AR_SYMB
%token <string> USER_VAL_TOK
%token EXISTS_TOK
%token FORALL_TOK
%token LET_TOK
%token FLET_TOK
%token SORTS_TOK
%token FUNS_TOK
%token PREDS_TOK
%token EXTENSIONS_TOK
%token DEFINITION_TOK
%token AXIOMS_TOK
%token LOGIC_TOK
%token COLON_TOK
%token LPAREN_TOK
%token RPAREN_TOK
%token LSQBRACKET_TOK
%token RSQBRACKET_TOK
%token SAT_TOK
%token UNSAT_TOK
%token UNKNOWN_TOK
%token ASSUMPTION_TOK
%token FORMULA_TOK
%token STATUS_TOK
%token BENCHMARK_TOK
%token EXTRASORTS_TOK
%token EXTRAFUNS_TOK
%token EXTRAPREDS_TOK
%token LANGUAGE_TOK
%token DOLLAR_TOK
%token QUESTION_MARK_TOK
%token EQUALS_TOK
%token SEMICOLON_TOK
%token EOF_TOK

%start benchmark
%type <Types.benchmark> benchmark

%%
benchmark:
    LPAREN_TOK BENCHMARK_TOK bench_name bench_attributes RPAREN_TOK
    {
      (* the whole benchmark *)
      if not (bench_attribute_exists "logic") then
        raise (ValidationError "No logic defined")
      else if not (bench_attribute_exists "status") then
        raise (ValidationError "No status defined")
      else 
        BENCH($3,get_bench_formula())
    }

bench_name:
    SYM_TOK 
    { 
      $1
    }

bench_attributes:
    bench_attribute bench_attributes {}
  | bench_attribute {}

bench_attribute:
    COLON_TOK ASSUMPTION_TOK an_formula 
    {
      add_bench_assumption $3
    }
  | COLON_TOK FORMULA_TOK an_formula 
    {
      set_bench_formula $3
    }
  | COLON_TOK STATUS_TOK status 
    {
      add_unique_bench_attribute ("status",Some $3)
    }
  | COLON_TOK LOGIC_TOK logic_name 
    {
      add_unique_bench_attribute ("logic",Some $3);
      Signature.load_logic $3
    }
  | COLON_TOK EXTRASORTS_TOK LPAREN_TOK sort_symb_decls RPAREN_TOK { }
  | COLON_TOK EXTRAFUNS_TOK LPAREN_TOK fun_symb_decls RPAREN_TOK { }
  | COLON_TOK EXTRAPREDS_TOK LPAREN_TOK pred_symb_decls RPAREN_TOK { }
  | annotation {
      let a1,a2 = $1 in
      add_bench_attribute (a1,a2)
    }

logic_name:
    SYM_TOK { $1 }
  | SYM_TOK parameters { 
      let rec paramstr p =
        match p with
            [] -> ""
          | [x] -> string_of_int x
          | h::t -> (string_of_int h)^":"^(paramstr t)
      in
      $1^"["^(paramstr $2)^"]"
    }

status:
    SAT_TOK {"sat"}
  | UNSAT_TOK {"unsat"}
  | UNKNOWN_TOK {"unknown"}

sort_symbs:
    sort_symb sort_symbs
    { 
      (* returns a list of sort names *)
      $1::$2
    }
  | sort_symb 
    { 
      (* returns a singleton list of one sort name *)
      [$1]
    }

sort_symb_decls:
    sort_symb_decls sort_symb_decl
    { 
      declare_sort $2
    }
  | sort_symb_decl 
    { 
      declare_sort $1
    }


fun_symb_decls:
    fun_symb_decls fun_symb_decl { $2::$1 }
  | fun_symb_decl { [$1] }



fun_symb_decl:
    LPAREN_TOK fun_symb sort_symbs annotations RPAREN_TOK
    {
    	declare_fun $2 (ANNOTATED_ARR ((fun_sort_list_to_sig $3),$4))
    }
  | LPAREN_TOK fun_symb sort_symbs RPAREN_TOK
    {
    	declare_fun $2 (fun_sort_list_to_sig $3)
    }

pred_symb_decls:
    pred_symb_decls pred_symb_decl {$2::$1}
  | pred_symb_decl {[$1]}

pred_symb_decl:
    LPAREN_TOK fun_symb sort_symbs annotations RPAREN_TOK
    {
    	declare_fun $2 (ANNOTATED_ARR (fun_sort_list_to_sig (append_bool $3),$4))
    }
  | LPAREN_TOK fun_symb annotations RPAREN_TOK
    {
    	declare_fun $2 (ANNOTATED_ARR (fun_sort_list_to_sig (append_bool []),$3))
    }
  | LPAREN_TOK fun_symb sort_symbs RPAREN_TOK
    {
    	declare_fun $2 (fun_sort_list_to_sig (append_bool $3))
    }
  | LPAREN_TOK fun_symb RPAREN_TOK
    {
    	declare_fun $2 (fun_sort_list_to_sig (append_bool []))
    }

an_formula:
    an_term 
    {if expression_is_formula $1 then
       $1
     else
       raise (ValidationError "Non-Boolean formula!")
    }

quant_vars:
    quant_vars quant_var 
    {
      (* returns a list of binders *)
      $2::$1
    }
  | quant_var 
    {
      (* returns a singleton list with one binder in it *)
      [$1]
    }

quant_var: 
    LPAREN_TOK variable sort_symb RPAREN_TOK
    {
    
      let vtype = $3 in
      let id = $2 in
      declare_var id vtype;
      (* returns the name of the variable along with the name of its sort *)
      (id,vtype)
    }

quant_symb:
    EXISTS_TOK 
    {
      (* pushes the variable scope *)
      push_var_scope();
      EXISTS
    }
  | FORALL_TOK 
    {
      (* pushes the variable scope *)
      push_var_scope();
      FORALL
    }


an_terms:
    an_term an_terms 
    {
      (* returns a list of terms *)
      $1::$2
    }
  | an_term 
    { 
      (* returns a singleton list of terms *)
      [$1]
    }

sort_symb_decl:
  simple_identifier 
  { 
    let (sid,_) = $1 in
    sid
  }

sort_symb:
  identifier {$1}

an_term:
    basic_term 
    { 
      (* returns a basic term with no annotations *)
      let t,s = $1 in
      EX(t,s)
    }
  | LPAREN_TOK basic_term annotations RPAREN_TOK 
    {
      (* adds annotations to a basic term and returns an annotated term *)
      let t,s = $2 in
      EXA(t,s,$3)
    }
  | LPAREN_TOK fun_symb an_terms annotations RPAREN_TOK
    {
      (* returns a function term with at least one argument with annotations *)
      let f,p = $2 in
      let param_sorts = List.map (fun x -> get_expression_sort x) $3 in
      let fun_sort = match_fun_sorts $2 param_sorts in
      EXA(FUN(f,p,$3),fun_sort,$4)
    }
  | LPAREN_TOK fun_symb an_terms RPAREN_TOK
    {
      (* returns a function term with at least one argument with no annotations *)
      let f,p = $2 in
      let param_sorts = List.map (fun x -> get_expression_sort x) $3 in
      let fun_sort = match_fun_sorts $2 param_sorts in
      EX(FUN(f,p,$3),fun_sort)
    }
  | LPAREN_TOK quant_symb quant_vars an_term annotations RPAREN_TOK
    {
      (* returns a quantified formula with annotations *)
      if not (expression_is_formula $4) then
        raise (TypeMismatch "Attempted to quantify non-bool expression");
      pop_var_scope();

      EXA(QUANT($2,$3,$4),bool_sort_return_type,$5)
    }
  | LPAREN_TOK quant_symb quant_vars an_term RPAREN_TOK
    {
      (* returns a quantified formula with no annotations *)
      if not (expression_is_formula $4) then
        raise (TypeMismatch "Attempted to quantify non-bool expression");
      pop_var_scope();

      EX(QUANT($2,$3,$4),bool_sort_return_type)
    }
  | LPAREN_TOK let_decl an_formula annotations RPAREN_TOK
    {
      (* returns a let formula with annotations *)
      let v,e = $2 in
      pop_var_scope();
      EXA(LET(v,e,$3),(get_expression_sort $3),$4)
    }
  | LPAREN_TOK let_decl an_formula RPAREN_TOK
    {
      (* returns a let formula with no annotations *)
      let v,e = $2 in
      pop_var_scope();
      EX(LET(v,e,$3),(get_expression_sort $3))
    }
  | LPAREN_TOK flet_decl an_formula annotations RPAREN_TOK
    {
      (* returns a flet formula with annotations *)
      let v,e = $2 in
      pop_var_scope();

      EXA(LET(v,e,$3),(get_expression_sort $3),$4)
    }
  | LPAREN_TOK flet_decl an_formula RPAREN_TOK
    {
      (* returns a flet formula with no annotations *)
      let v,e = $2 in
      pop_var_scope();
      EX(LET(v,e,$3),(get_expression_sort $3))
    }
  | LPAREN_TOK an_term RPAREN_TOK
    { 
      (* too many parentheses *)
      raise (ValidationError "SMT-LIB does not allow arbitrary nesting of parentheses!")
    }

let_decl:
  LET_TOK LPAREN_TOK var an_term RPAREN_TOK
  {
      (* a let declaration *)
      (* pushes variable scope *)
      push_var_scope();
      (* flets mut be bool *)
      if expression_is_formula $4 then
        raise (TypeMismatch "LET used with bool expression");
      let vtype = get_expression_sort $4 in
      let id = $3 in
      declare_var id vtype;
      (id,$4)
  }
flet_decl:
  FLET_TOK LPAREN_TOK fvar an_term RPAREN_TOK
  {
      (* a flet declaration *)
      (* pushes variable scope *)
      push_var_scope();
      if not (expression_is_formula $4) then
        raise (TypeMismatch "FLET used with non-bool expression");
      let vtype = bool_sort_return_type in
      let id = $3 in
      declare_var id vtype;
      (id,$4)
  }

basic_term:
    var 
    { 
      (* returns a variable term with its sort (i.e., a return_type) *)
      VAR($1),(get_var_sort $1)
    }
  | fvar 
    { 
      (* returns a boolean variable *)
      VAR($1),bool_sort_return_type
    }
  | numeral
    {
      (* returns a numeral term with its return_type *)
      $1
    }
  | rational
    {
      (* returns a rational term with its return_type *)
      $1
    }
  | fun_symb 
    {
      (* returns a function term with no arguments (a constant) *)
      let f,p = $1 in (* note: we strip off the symbol indices here! *)
      FUN(f,[],[]),(match_fun_sorts $1 [])
    }



annotations:
    annotation annotations 
    { 
      (* returns a list of annotations *)
      ($1::$2)
    }
  | annotation 
    {
      (* returns a singleton list of annotations *)
      [$1]
    }

annotation:
    attribute 
    {
      (* returns the attribute's name and None because it doesn't have a corresponding value *)
      ($1,None)
    }
  | attribute user_value 
    {
      (* returns the attribute's name along with its corresponding value *)
      ($1,Some $2)
    }

user_value:
    USER_VAL_TOK
    {
      $1
    }
  | STRING_TOK
    {
      $1
    }

fun_symb:
    identifier
    {
        $1
    }
  | AR_SYMB 
    { 
      let id = get_id_num_from_symbol $1 in
      (SYM_ID(id,0),[])
    }

attribute:
    COLON_TOK SYM_TOK { 
      $2
    }

rational:
  RATIONAL_TOK { FUN(SYM_ID(get_id_num_from_symbol $1,0),[],[]),(get_real_sort_id,[]) }

numeral:
    number { 
      FUN(SYM_ID(get_id_num_from_symbol $1,0),[],[]),(get_numeral_sort []) 
    }
  | BVNUMERAL_TOK { 
      FUN(SYM_ID(get_id_num_from_symbol $1,0),[],[]),(get_numeral_sort []) 
    }
  | BVNUMERAL_TOK parameters { 
      if List.length $2 = 1 then
        begin
          let nsym = SYM_ID(get_id_num_from_symbol $1,0) in
          mark_numeral_as_indexed nsym;
          FUN(nsym,[],[]),(get_numeral_sort $2) 
        end
      else
        raise Parse_error
    }
  | BVBINNUMERAL_TOK {
      let sz = (String.length $1) - 5 in
      FUN(SYM_ID(get_id_num_from_symbol $1,0),[],[]),(get_numeral_sort [sz])
    }
  | BVHEXNUMERAL_TOK { 
      let sz = ((String.length $1) - 5)*4 in
      FUN(SYM_ID(get_id_num_from_symbol $1,0),[],[]),(get_numeral_sort [sz])
    }

number:
  NUMERAL_TOK { $1 }

parameter_list:
    number { [(int_of_string $1)] }
  | number COLON_TOK parameter_list { (int_of_string $1)::$3 }

parameters:
  | LSQBRACKET_TOK parameter_list RSQBRACKET_TOK
    { $2 }

variable:
    var {$1}
  | fvar {$1}

var:
  VAR_TOK {
      let id = get_id_num_from_symbol $1 in
      SYM_ID(id,0)
  }

fvar:
  FVAR_TOK {
      let id = get_id_num_from_symbol $1 in
      SYM_ID(id,0)
  }

identifier:
  | simple_identifier { $1 }
  | indexed_identifier { $1 }
  
indexed_identifier:
  simple_identifier parameters
  { let (SYM_ID(x,_),_) = $1 in
    SYM_ID(x,List.length $2),$2
  }

simple_identifier:
  SYM_TOK { 
    let id = get_id_num_from_symbol $1 in
    SYM_ID(id,0),[]
  }

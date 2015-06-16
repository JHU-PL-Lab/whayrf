(**
   Contains data type definitions for the AST of the *nested* whayrf language.
*)

open Batteries;;
open Whayrf_ast;;
open Whayrf_ast_uid;;
open Whayrf_utils;;

(** Expressions in the nested language. *)
type expr =
  | Record_expr of Ident_set.t
  | Function_expr of function_value
  | Var_expr of var
  | Appl_expr of expr * expr
  | Conditional_expr of expr * pattern * function_value * function_value
  | Let_expr of var * expr * expr

(** Function values in the nested language. *)
and function_value =
  | Function of var * expr

(** Patterns in the nested language. *)
and pattern =
  | Record_pattern of Ident_set.t
;;

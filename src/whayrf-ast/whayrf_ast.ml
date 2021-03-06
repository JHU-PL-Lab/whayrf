(**
   Contains data type definitions for the whayrf language AST.
*)

open Batteries;;
open Whayrf_ast_uid;;
open Whayrf_utils;;

(** A module for hashtables keyed by UIDs. *)
module Ast_uid_hashtbl = Whayrf_ast_uid.Ast_uid_hashtbl;;

(** A data type for identifiers in the whayrf language. *)
type ident = Ident of string;;

module Ident_hash =
struct
  type t = ident
  let equal = (=)
  let hash = Hashtbl.hash
end
;;

module Ident_hashtbl = Hashtbl.Make(Ident_hash);;

module Ident_order =
struct
  type t = ident
  let compare = compare
end
;;

module Ident_set = Set.Make(Ident_order);;

module Ident_map = Map.Make(Ident_order);;

(** A freshening stack of identifiers for variables produced at runtime.  This
    tracks the invocation stack of these variables.  The first element in the
    list is the topmost element in the stack.  If this stack is absent, then
    the variable in question has not been instantiated (and remains within the
    body of a function). *)
type freshening_stack = Freshening_stack of ident list;;

(** Variables in the AST. *)
type var = Var of ident * freshening_stack option;;

module Var_order =
struct
  type t = var
  let compare = compare
end;;

module Var_set = Set.Make(Var_order);;

module Var_map = Map.Make(Var_order);;

module Var_hashtbl = Hashtbl.Make(
  struct
    type t = var
    let equal = (=)
    let hash = Hashtbl.hash
  end
);;

(** A type to express whayrf record values. *)
type record_value = Record_value of var Ident_map.t

(** A type to express whayrf function values. *)
and function_value = Function_value of var * expr

(** A type to represent values. *)
and value =
  | Value_record of record_value
  | Value_function of function_value

(** A type to represent the bodies of clauses. *)
and clause_body =
  | Value_body of value
  | Var_body of var
  | Appl_body of var * var
  | Projection_body of var * ident
  | Conditional_body of var * pattern * function_value * function_value

(** A type to represent clauses. *)
and clause = Clause of var * clause_body

(** A type to represent expressions. *)
and expr = Expr of clause list

(** A type representing patterns. *)
and pattern =
  | Record_pattern of pattern Ident_map.t
  | Function_pattern of pattern * pattern
;;

module Pattern_order =
struct
  type t = pattern
  let compare = compare
end;;

module Pattern_set = Set.Make(Pattern_order);;

(**
   Utils to manipulate the AST.
*)

(** Counter used to provide new fresh pattern variables. *)
let fresh_pattern_variable_counter = ref 0;;

(** Perform substitution on patterns. It's the operation represented by
    $\pi\[\beta \ \beta'\]$. A.k.a. alpha substitution. *)
let rec rename_pattern_variable pattern new_pattern_variable old_pattern_variable =
  match pattern with
  | Record_pattern (pattern_elements) ->
    Record_pattern (
      Ident_map.map
        (
          fun subpattern ->
            rename_pattern_variable subpattern new_pattern_variable old_pattern_variable
        )
        pattern_elements
    )
  | Function_pattern (function_pattern, parameter_pattern) ->
    Function_pattern (
      rename_pattern_variable function_pattern new_pattern_variable old_pattern_variable,
      rename_pattern_variable parameter_pattern new_pattern_variable old_pattern_variable
    )
;;

open Batteries;;

open Whayrf_ast;;
open Whayrf_ast_pretty;;
open Whayrf_consistency;;
open Whayrf_initial_alignment;;
open Whayrf_logger;;
open Whayrf_notation;;
open Whayrf_pattern_subsumption;;
open Whayrf_type_compatibility;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

let logger = make_logger "Whayrf_function_pattern_search";;

(** The function_type-pattern pair used in the main paper for cycle detection
    and returned by FUN PATS. *)
type function_pattern_matching_case = Function_pattern_matching_case of function_type * pattern;;

module Function_pattern_matching_case_order =
struct
  type t = function_pattern_matching_case
  let compare = compare
end
;;
module Function_pattern_matching_case_set = Set.Make(Function_pattern_matching_case_order);;

(** Function Pattern Search looks for all pairs of function types and patterns
    that can be explored by subordinate closures. It comes in three flavors, one
    that takes a raw type (ttype), one that takes a restricted type and another
    that takes a type variable.

    The rules come from Function Pattern Search in the appendix, but instead of
    returning squelch constraints, it returns function_pattern_matching_cases,
    as per FUN PATS in the main paper. *)
let rec function_pattern_search_ttype ttype constraint_set pattern =
  match (ttype, pattern) with
  (* FUNCTION *)
  | (
    Function_type_type (
      function_type
    ),
    Function_pattern (
      _
    )
  ) ->
    Function_pattern_matching_case_set.singleton
      (Function_pattern_matching_case (function_type, pattern))

  (* RECORD *)
  (* Align the record type with the record pattern and recurse on the type
     variable under the record label. This implementation doesn't apply the rule
     once, but performs the fixpoint and returns the resulting set. *)
  | (
    Record_type (record_elements),
    Record_pattern (pattern_elements)
  ) ->
    record_elements
    |> Ident_map.enum
    |> Enum.map
      (
        fun (record_label, type_variable) ->
          pattern_elements
          |> Ident_map.enum
          |> Enum.filter_map
            (
              fun (pattern_label, pattern) ->
                if record_label = pattern_label then
                  Some (
                    function_pattern_search_type_variable
                      type_variable
                      constraint_set
                      pattern
                  )
                else
                  None
            )
          |> Enum.fold Function_pattern_matching_case_set.union Function_pattern_matching_case_set.empty
      )
    |> Enum.fold Function_pattern_matching_case_set.union Function_pattern_matching_case_set.empty

  | _ ->
    Function_pattern_matching_case_set.empty

(** FILTERED TYPE *)
(* Simply ignore the filter. *)
and function_pattern_search_restricted_type
    (Restricted_type (ttype, _))
    constraint_set
    pattern =
  function_pattern_search_ttype ttype constraint_set pattern

(** TYPE SELECTION *)
(* This implementation doesn't apply the rule once, but performs the fixpoint
   and returns the resulting set. *)
and function_pattern_search_type_variable type_variable constraint_set pattern =
  logger `trace ("Looking for type variable `" ^ pretty_type_variable type_variable ^ "' in the constraint set: `"  ^ pretty_constraint_set constraint_set ^ "', and matching it with pattern `" ^ pretty_pattern pattern ^ "'.");
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Restricted_type_lower_bound (restricted_type),
            other_type_variable
          ) ->
          if type_variable = other_type_variable then
            Some (function_pattern_search_restricted_type restricted_type constraint_set pattern)
          else
            None
        | _ -> None
    )
  |> Enum.fold Function_pattern_matching_case_set.union Function_pattern_matching_case_set.empty
;;

(** Find all function pattern matching cases in a constraint set.

    It's inspired by FUN PATS.*)
let function_pattern_search constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Conditional_lower_bound (
              type_variable,
              pattern,
              _,
              _
            ),
            _
          )
        | Type_variable_constraint (type_variable, pattern) ->
          Some (
            function_pattern_search_type_variable
              type_variable
              constraint_set
              pattern
          )
        | _ ->
          None
    )
  |> Enum.fold Function_pattern_matching_case_set.union Function_pattern_matching_case_set.empty
;;

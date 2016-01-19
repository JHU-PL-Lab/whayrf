open Batteries;;

open Whayrf_ast;;
open Whayrf_function_pattern_search;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_types_utils;;
open Whayrf_utils;;

(** Affection is a concept necessary to implement the dependency graph
    resolution. It records the fact that `a -affects-> b'. A closure is
    performed on the `<<C' rules to build an `affection_set'. From the
    `affection_set' the dependency graph is devised. *)
type affection =
  | Type_variable_type_variable_affection of type_variable * type_variable
  | Type_variable_function_pattern_matching_case_affection of type_variable * function_pattern_matching_case
  | Function_pattern_matching_case_type_variable_affection of function_pattern_matching_case * type_variable
;;

module Affection_order =
struct
  type t = affection
  let compare = compare
end
;;
module Affection_set = Set.Make(Affection_order);;

(** VARIABLE *)
let close_by_variable affection_set constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Type_variable_lower_bound (
              type_variable_before
            ),
            type_variable_after
          )
          ->
          Some (
            Type_variable_type_variable_affection (
              type_variable_before,
              type_variable_after
            )
          )

        | _ -> None
    )
  |> Affection_set.of_enum
  |> Affection_set.union affection_set
;;

(* TODO: Not implemented. *)
let close_by_reflexivity affection_set constraint_set =
  affection_set
;;

(* TODO: Not implemented. *)
let close_by_transitivity affection_set constraint_set =
  affection_set
;;

(* TODO: Not implemented. *)
let close_by_application affection_set constraint_set =
  affection_set
;;

(* TODO: Not implemented. *)
let close_by_conditional_input affection_set constraint_set =
  affection_set
;;

(* TODO: Not implemented. *)
let close_by_conditional_output affection_set constraint_set =
  affection_set
;;

(* TODO: Not implemented. *)
let close_by_conditional_success_body affection_set constraint_set =
  affection_set
;;

(* TODO: Not implemented. *)
let close_by_conditional_failure_body affection_set constraint_set =
  affection_set
;;

(* TODO: Not implemented. *)
let close_by_record affection_set constraint_set =
  affection_set
;;

(** Run a list of affection closure rules to a fixpoint. *)
let rec affection_closure_fixpoint rules affection_set constraint_set =
  let augmented_affection_set =
    List.fold_left
      (
        fun affection_set rule ->
          rule affection_set constraint_set
      )
      affection_set
      rules
  in
  if Affection_set.equal affection_set augmented_affection_set then
    affection_set
  else
    affection_closure_fixpoint rules augmented_affection_set constraint_set
;;

let affection_closure constraint_set =
  affection_closure_fixpoint
    [
      (* The order is irrelevant for the correctness of the program. *)
      close_by_variable;
      close_by_reflexivity;
      close_by_transitivity;
      close_by_application;
      close_by_conditional_input;
      close_by_conditional_output;
      close_by_conditional_success_body;
      close_by_conditional_failure_body;
      close_by_record
    ]
    Affection_set.empty
    constraint_set
;;

(** ≺C *)
let is_dependency
    potential_dependency_function_pattern_matching_case
    dependent_function_pattern_matching_case
    affections
    constraint_set =
  (
    (* A `function_pattern_matching_case' cannot be a dependency of itself. *)
    dependent_function_pattern_matching_case <>
    potential_dependency_function_pattern_matching_case
  ) &&
  let type_variables_in_constraint_set =
    type_variables_in constraint_set
  in
  type_variables_in_constraint_set
  |> Type_variable_set.enum
  |> Enum.exists
    (
      fun type_variable_1 ->
        type_variables_in_constraint_set
        |> Type_variable_set.enum
        |> Enum.exists
          (
            fun type_variable_2 ->
              List.enum [
                Function_pattern_matching_case_type_variable_affection (
                  potential_dependency_function_pattern_matching_case,
                  type_variable_1
                );
                Type_variable_type_variable_affection (
                  type_variable_1,
                  type_variable_2
                );
                Type_variable_function_pattern_matching_case_affection (
                  type_variable_2,
                  dependent_function_pattern_matching_case
                )
              ]
              |> Enum.for_all
                (
                  fun requirement ->
                    Affection_set.mem
                      requirement
                      affections
                )
          )
    )
;;

let dependency_resolution constraint_set =
  Dependency_graph (
    let function_pattern_matching_cases =
      function_pattern_search constraint_set
    in
    let affections =
      affection_closure constraint_set
    in
    function_pattern_matching_cases
    |> Function_pattern_matching_case_set.enum
    |> Enum.map
      (
        fun dependent_function_pattern_matching_case ->
          (
            dependent_function_pattern_matching_case,
            function_pattern_matching_cases
            |> Function_pattern_matching_case_set.enum
            |> Enum.filter
              (
                fun potential_dependency_function_pattern_matching_case ->
                  is_dependency
                    potential_dependency_function_pattern_matching_case
                    dependent_function_pattern_matching_case
                    affections
                    constraint_set
              )
            |> Function_pattern_matching_case_set.of_enum
          )
      )
    |> Function_pattern_matching_case_map.of_enum
  )
;;

(* TODO: Not implemented. *)
(** Inspired by BLOCKING and CYCLE BREAKER from the main paper submission. *)
let function_pattern_matching_cases_participating_in_cycles dependency_graph =
  Function_pattern_matching_case_set.empty
;;

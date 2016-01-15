open Batteries;;

open Whayrf_ast;;
open Whayrf_function_pattern_search;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_types_utils;;
open Whayrf_utils;;

(* TODO: Not implemented. *)
let before
    potential_dependency_function_pattern_matching_case
    dependent_function_pattern_matching_case
    constraint_set =
  false
;;

let dependency_resolution constraint_set =
  Dependency_graph (
    let function_pattern_matching_cases =
      function_pattern_search constraint_set
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
                  before
                    potential_dependency_function_pattern_matching_case
                    dependent_function_pattern_matching_case
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

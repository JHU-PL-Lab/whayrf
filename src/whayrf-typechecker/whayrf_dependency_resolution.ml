open Batteries;;

open Whayrf_ast;;
open Whayrf_function_pattern_search;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_types_utils;;
open Whayrf_utils;;

(* TODO: Not implemented. *)
let dependency_resolution constraint_set =
  Dependency_graph (
    function_pattern_search constraint_set
    |> Function_pattern_matching_case_set.enum
    |> Enum.map
      (
        fun function_pattern_matching_case ->
          (
            function_pattern_matching_case,
            Function_pattern_matching_case_set.empty
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

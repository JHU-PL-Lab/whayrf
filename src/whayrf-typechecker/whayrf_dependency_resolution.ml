open Batteries;;

open Whayrf_ast;;
open Whayrf_types;;

type dependency_graph = Dependency_graph of
    Function_pattern_matching_case_set.t Function_pattern_matching_case_map.t;;

(* TODO: Not implemented. *)
let pretty_dependency_graph dependency_graph =
  "TODO"
;;

(* TODO: Not implemented. *)
let dependency_resolution constraint_set =
  Dependency_graph (
    Function_pattern_matching_case_map.empty
  )
;;

(* TODO: Not implemented. *)
let dependencies function_pattern_matching_case dependency_graph =
  Function_pattern_matching_case_set.empty
;;

(* TODO: Not implemented. *)
(** Inspired by BLOCKING and CYCLE BREAKER from the main paper submission. *)
let function_pattern_matching_cases_participating_in_cycles dependency_graph =
  Function_pattern_matching_case_set.empty
;;

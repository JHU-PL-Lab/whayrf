open Batteries;;

open Whayrf_ast;;
open Whayrf_function_pattern_search;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

type dependency_graph =
  | Dependency_graph of
      Function_pattern_matching_case_set.t Function_pattern_matching_case_map.t
;;

let pretty_dependency_graph (
    Dependency_graph dependency_graph_elements
  ) =
  let graphviz_function_pattern_matching_case function_pattern_matching_case =
    "\"" ^ pretty_function_pattern_matching_case function_pattern_matching_case ^ "\""
  in
  "Graphviz source code:\ndigraph {" ^
  (
    dependency_graph_elements
    |> Function_pattern_matching_case_map.enum
    |> Enum.map
      (
        fun (
          this_function_pattern_matching_case,
          this_function_pattern_matching_case_dependencies
        ) ->
          graphviz_function_pattern_matching_case this_function_pattern_matching_case ^
          ";" ^ (
            this_function_pattern_matching_case_dependencies
            |> Function_pattern_matching_case_set.enum
            |> Enum.map
              (
                fun this_function_pattern_matching_case_dependency ->
                  graphviz_function_pattern_matching_case this_function_pattern_matching_case ^ " -> " ^
                  graphviz_function_pattern_matching_case this_function_pattern_matching_case_dependency ^ ";"
              )
            |> Enum.fold (^) ""
          )
      )
    |> Enum.fold (^) ""
  ) ^ "}"
;;

let dependencies function_pattern_matching_case (
    (Dependency_graph dependency_graph_elements)
    as dependency_graph
  ) =
  if Function_pattern_matching_case_map.mem function_pattern_matching_case dependency_graph_elements then
    Function_pattern_matching_case_map.find function_pattern_matching_case dependency_graph_elements
  else
    raise @@ Invariant_failure (
      "`function_pattern_matching_case' = `" ^
      pretty_function_pattern_matching_case function_pattern_matching_case ^
      "' not found in `dependency_graph' = `" ^
      pretty_dependency_graph dependency_graph ^ "'."
    )
;;

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

open Batteries;;

open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

(** Retrieve dependencies of a `function_pattern_matching_case' in a
    `dependency_graph'. *)
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

(** Find all type variables in `constraint_set'. *)
(* TODO: Not implemented. *)
let type_variables_in constraint_set =
  Type_variable_set.empty
;;

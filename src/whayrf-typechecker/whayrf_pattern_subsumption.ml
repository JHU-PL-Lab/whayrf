open Batteries;;

open Whayrf_ast;;
open Whayrf_initial_alignment;;
open Whayrf_notation;;
open Whayrf_pattern_constraint_solver;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

(** Implements the Pattern Subsumption rules which determines if a pattern is
    compatible with every type that another pattern would be compatible. *)
let is_subsumption_pattern pattern_1 pattern_2 =
  let rec step pattern_constraint_set =
    try
      let pattern_constraint_closed_pattern_constraint_set =
        perform_pattern_constraint_closure pattern_constraint_set
      in
      if Pattern_constraint_set.is_empty pattern_constraint_closed_pattern_constraint_set then
        true
      else
        pattern_constraint_closed_pattern_constraint_set
        |> perform_transitive_pattern_closure
        |> filter_out_wobbly_variables
        |> step
    with
    | Contradiction_found -> false
  in
  step @@ initial_alignment pattern_1 pattern_2
;;

(** P-N PATTERN SETS *)
let is_subsumption_pattern_set
    (Positive_pattern_set (positive_patterns))
    (Negative_pattern_set (negative_patterns))
  =
  positive_patterns
  |> Pattern_set.enum
  |> Enum.exists
    (
      fun positive_pattern ->
        negative_patterns
        |> Pattern_set.enum
        |> Enum.exists
          (
            fun negative_pattern ->
              is_subsumption_pattern positive_pattern negative_pattern
          )
    )
;;

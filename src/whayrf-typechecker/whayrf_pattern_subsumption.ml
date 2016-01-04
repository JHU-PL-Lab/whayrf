open Batteries;;

open Whayrf_ast;;
open Whayrf_initial_alignment;;
open Whayrf_notation;;
open Whayrf_pattern_constraint_solver;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

(** Pattern Subsumption relation, which determines if a pattern is compatible
    with every type that another pattern would be compatible with. *)
let rec is_subsumption_pattern pattern_1 pattern_2 =
  match (pattern_1, pattern_2) with

  (* RECORD *)
  | (
    Record_pattern (pattern_1_elements),
    Record_pattern (pattern_2_elements)
  ) ->
    pattern_2_elements
    |> Ident_map.enum
    |> Enum.for_all
      (
        fun (pattern_2_label, pattern_2_subpattern) ->
          pattern_1_elements
          |> Ident_map.enum
          |> Enum.exists
            (
              fun (pattern_1_label, pattern_1_subpattern) ->
                (pattern_1_label = pattern_2_label) &&
                is_subsumption_pattern pattern_1_subpattern pattern_2_subpattern
            )
      )

  (* FUNCTION *)
  | (
    Function_pattern (pattern_1_parameter_pattern, pattern_1_return_pattern),
    Function_pattern (pattern_2_parameter_pattern, pattern_2_return_pattern)
  ) ->
    is_subsumption_pattern pattern_2_parameter_pattern pattern_1_parameter_pattern &&
    is_subsumption_pattern pattern_1_return_pattern pattern_2_return_pattern

  | _ -> false
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

open Batteries;;

open Whayrf_ast;;
open Whayrf_initial_alignment;;
open Whayrf_notation;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

(** Implements the Pattern Subsumption rules which determines if a pattern is
    compatible with every type that another pattern would be compatible. *)
let rec is_subsumption_pattern pattern_1 pattern_2 =
  match (pattern_1, pattern_2) with
  (* RECORD *)
  | (
    Record_pattern (record_patterns_1),
    Record_pattern (record_patterns_2)
  ) ->
    record_patterns_2
    |> Ident_map.enum
    |> Enum.for_all
      (
        fun (label_2, pattern_2) ->
          record_patterns_1
          |> Ident_map.enum
          |> Enum.exists
            (
              fun (label_1, pattern_1) ->
                (label_1 = label_2) &&
                (is_subsumption_pattern pattern_1 pattern_2)
            )
      )

  (* FUNCTION *)
  | (
    Function_pattern (function_pattern_1, parameter_pattern_1),
    Function_pattern (function_pattern_2, parameter_pattern_2)
  ) ->
    (is_subsumption_pattern parameter_pattern_1 parameter_pattern_2) &&
    (is_subsumption_pattern function_pattern_2 function_pattern_1)

  (* VARIABLE *)
  | (
    Pattern_variable_pattern _,
    Pattern_variable_pattern _
  ) ->
    pattern_1 = pattern_2

  (* FORALL ELIM *)
  | (
    Forall_pattern (ident, sub_pattern_1),
    _
  ) ->
    (* TODO: Not implemented yet. *)
    false

  (* FORALL INTRO *)
  | (
    _,
    Forall_pattern (old_pattern_variable, sub_pattern_2)
  ) ->
    let new_pattern_variable = new_fresh_pattern_variable () in
    let renamed_pattern =
      rename_pattern_variable
        sub_pattern_2
        new_pattern_variable
        old_pattern_variable
    in
    is_subsumption_pattern pattern_1 renamed_pattern

  (* Fallback *)
  | _ -> false

(** P-N PATTERN SETS *)
and is_subsumption_pattern_set
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

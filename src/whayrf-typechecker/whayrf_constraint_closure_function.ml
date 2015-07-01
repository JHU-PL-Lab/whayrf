open Batteries;;

open Whayrf_ast;;
open Whayrf_consistency;;
open Whayrf_constraint_closure_non_function;;
open Whayrf_function_pattern_search;;
open Whayrf_initial_alignment;;
open Whayrf_notation;;
open Whayrf_pattern_subsumption;;
open Whayrf_type_compatibility;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

(** Perform Function Constraint Closure (i.e. the one with the F superscript).

    This function doesn't perform a single step, but the fixpoint (omega). This
    returns the augmented constraint set with the new constraints as well as the
    original constraints. *)

(** FUNCTION CLOSURE *)
let perform_function_closure constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Conditional_lower_bound (
              subject_type_variable,
              pattern,
              _,
              _
            ),
            _
          ) ->
          Some (function_pattern_search_type_variable subject_type_variable constraint_set pattern)
        | _ -> None
    )
  |> Enum.fold Constraint_set.union constraint_set
;;

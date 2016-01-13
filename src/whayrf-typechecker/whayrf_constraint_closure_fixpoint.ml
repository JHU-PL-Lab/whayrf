open Batteries;;

open Whayrf_ast;;
open Whayrf_consistency;;
open Whayrf_initial_alignment;;
open Whayrf_notation;;
open Whayrf_pattern_subsumption;;
open Whayrf_type_compatibility;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

(** Run a list of closure rules to a fixpoint. *)
let rec closure_fixpoint rules constraint_set =
  let new_constraints =
    List.fold_left
      (
        fun accumulated_new_constraints rule ->
          Constraint_set.union constraint_set accumulated_new_constraints
          |> rule
          |> Constraint_set.union accumulated_new_constraints
      )
      Constraint_set.empty
      rules
  in
  if new_constraints = Constraint_set.empty then
    Constraint_set.empty
  else
    Constraint_set.union constraint_set new_constraints
    |> closure_fixpoint rules
    |> Constraint_set.union new_constraints
;;

open Batteries;;

open Whayrf_ast;;
open Whayrf_consistency;;
open Whayrf_constraint_closure_function;;
open Whayrf_constraint_closure_non_function;;
open Whayrf_function_pattern_search;;
open Whayrf_initial_alignment;;
open Whayrf_logger;;
open Whayrf_notation;;
open Whayrf_pattern_subsumption;;
open Whayrf_type_compatibility;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

let logger = make_logger "Whayrf_constraint_closure";;

(** Perform Constraint Closure (i.e. the one with no superscript).

    This function doesn't perform a single step, but the fixpoint (omega). This
    returns the augmented constraint set with the new constraints as well as the
    original constraints. *)
let rec perform_closure constraint_set =
  logger `trace ("Performing constraint closure with constraint set: `" ^ pretty_constraint_set constraint_set ^ "'.");
  (* The order in which operations happen here is fundamental for the correct
     behavior of the program. *)
  let closure_functions =
    [
      perform_non_function_closure;
      perform_function_closure
    ]
  in
  let augmented_constraint_set =
    List.fold_left
      (
        fun partially_augmented_constraint_set closure_function ->
          let inferred_constraints = closure_function perform_closure partially_augmented_constraint_set in
          Constraint_set.union partially_augmented_constraint_set inferred_constraints
      )
      constraint_set
      closure_functions
  in
  if (Enum.count (Constraint_set.enum constraint_set)) <>
     (Enum.count (Constraint_set.enum augmented_constraint_set)) then
    perform_closure augmented_constraint_set
  else
    augmented_constraint_set
;;

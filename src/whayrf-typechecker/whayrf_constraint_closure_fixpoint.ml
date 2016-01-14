open Batteries;;
open Printf;;

open Whayrf_ast;;
open Whayrf_consistency;;
open Whayrf_initial_alignment;;
open Whayrf_notation;;
open Whayrf_logger;;
open Whayrf_pattern_subsumption;;
open Whayrf_type_compatibility;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

let logger = make_logger "Whayrf_constraint_fixpoint";;

(** Run a list of closure rules to a fixpoint. *)
let rec closure_fixpoint rules constraint_set =
  logger `trace
    (sprintf
       "`closure_fixpoint' called with `constraint_set' = `%s'."
       (pretty_constraint_set constraint_set)
    )
  ;

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
  logger `trace
    (sprintf
       "`closure_fixpoint' found `new_constraints' = `%s'."
       (pretty_constraint_set new_constraints)
    )
  ;
  if new_constraints = Constraint_set.empty then
    Constraint_set.empty
  else
    Constraint_set.union constraint_set new_constraints
    |> closure_fixpoint rules
    |> Constraint_set.union new_constraints
;;

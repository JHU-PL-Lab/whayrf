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

  let augmented_constraint_set =
    List.fold_left
      (|>)
      constraint_set
      rules
  in
  logger `trace
    (sprintf
       "`closure_fixpoint' `augmented_constraint_set' = `%s'."
       (pretty_constraint_set augmented_constraint_set)
    )
  ;
  if Constraint_set.equal constraint_set augmented_constraint_set then
    constraint_set
  else
    closure_fixpoint rules augmented_constraint_set
;;

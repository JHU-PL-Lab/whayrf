(**
  This module represents the entry point for the Whayrf typechecking process.
*)

open Batteries;;
open Printf;;

open Whayrf_ast_pretty;;
open Whayrf_consistency;;
open Whayrf_constraint_closure;;
open Whayrf_initial_alignment;;
open Whayrf_types;;
open Whayrf_types_pretty;;

(* ************************************************************************** *)
(* LOGGER *)

let logger = Whayrf_logger.make_logger "Whayrf_typechecker";;

(* ************************************************************************** *)
(* TYPECHECKING *)

(**
  Performs typechecking of the provided expression.
  @param e The expression to typecheck.
  @return [true] if the expression typechecks; [false] if it does not.
*)
let typecheck e =
  (* Step 1: Initially align the expression. *)
  let Constrained_type (_, constraint_set) = initial_align_expr e in
  logger `trace
    (sprintf
      "Initial alignment of %s yields constraints %s"
      (pretty_expr e) (pretty_constraint_set constraint_set)
    )
  ;
  (* Step 2: Perform constraint closure. *)
  let constraint_set' = perform_closure constraint_set in
  logger `trace
    (sprintf
      "Constraint closure yields constraints %s"
      (pretty_constraint_set constraint_set')
    )
  ;
  (* Step 3: Look for inconsistencies. *)
  (is_consistent constraint_set', build_dispatch_table constraint_set')
  ;;

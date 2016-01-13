(**
  This module represents the entry point for the Whayrf typechecking process.
*)

open Batteries;;
open Printf;;

open Whayrf_ast_pretty;;
open Whayrf_consistency;;
open Whayrf_constraint_closure_full;;
open Whayrf_constraint_closure_ordering;;
open Whayrf_dependency_resolution;;
open Whayrf_dispatch_table;;
open Whayrf_initial_alignment;;
open Whayrf_types;;
open Whayrf_types_pretty;;

let logger = Whayrf_logger.make_logger "Whayrf_typechecker";;

let typecheck expression =
  (* Initial alignment. *)
  let Constrained_type (_, initial_constraint_set) = initial_align_expr expression in
  logger `trace
    (sprintf
      "Initial alignment of %s yields constraints %s"
      (pretty_expr expression) (pretty_constraint_set initial_constraint_set)
    )
  ;
  (* Ordering constraint closure *)
  let dependency_graph_constraint_set =
    ordering_closure initial_constraint_set
  in
  (* Dependency resolution *)
  let dependency_graph =
    dependency_resolution dependency_graph_constraint_set
  in
  (* Full constraint closure *)
  let full_constraint_set =
    full_closure dependency_graph initial_constraint_set
  in
  logger `trace
    (sprintf
      "Full constraint closure yields constraints %s"
      (pretty_constraint_set full_constraint_set)
    )
  ;
  (* Immediately consistent? *)
  (is_consistent full_constraint_set, build_dispatch_table full_constraint_set)
;;

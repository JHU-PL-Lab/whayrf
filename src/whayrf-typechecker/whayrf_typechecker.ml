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
  logger `trace
    (sprintf
      "Typechecking expression `%s'."
      (pretty_expr expression)
    )
  ;
  (* Initial alignment. *)
  let Constrained_type (_, initial_constraint_set) = initial_align_expr expression in
  logger `trace
    (sprintf
      "Initial constraint set `%s'."
      (pretty_constraint_set initial_constraint_set)
    )
  ;
  (* Ordering constraint closure *)
  let dependency_graph_constraint_set =
    ordering_closure initial_constraint_set
  in
  logger `trace
    (sprintf
      "Dependency graph constraint set `%s'."
      (pretty_constraint_set dependency_graph_constraint_set)
    )
  ;
  (* Dependency resolution *)
  let dependency_graph =
    dependency_resolution dependency_graph_constraint_set
  in
  logger `trace
    (sprintf
      "Dependency graph `%s'."
      (pretty_dependency_graph dependency_graph)
    )
  ;
  (* Full constraint closure *)
  let full_constraint_set =
    full_closure dependency_graph initial_constraint_set
  in
  logger `trace
    (sprintf
      "Full constraint set `%s'."
      (pretty_constraint_set dependency_graph_constraint_set)
    )
  ;
  (* Immediately consistent? *)
  (is_consistent full_constraint_set, build_dispatch_table full_constraint_set)
;;

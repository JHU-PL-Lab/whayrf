open Batteries;;
open Printf;;

open Whayrf_constraint_closure_fixpoint;;
open Whayrf_constraint_closure_non_function;;
open Whayrf_constraint_closure_ordering_function;;
open Whayrf_logger;;
open Whayrf_types_pretty;;

let logger = make_logger "Whayrf_constraint_closure_ordering";;

(** Ordering-function constraint closure (O superscript) *)
let ordering_closure constraint_set =
  logger `trace
    (sprintf
       "`ordering_closure' called with `constraint_set' = `%s'."
       (pretty_constraint_set constraint_set)
    )
  ;
  closure_fixpoint
    [
      (* The order _is relevant_ for the correctness of the program.

         It's the same as the order in Full constraint closure. *)
      non_function_closure;
      ordering_function_closure
    ]
    constraint_set
;;

open Batteries;;
open Printf;;

open Whayrf_constraint_closure_fixpoint;;
open Whayrf_constraint_closure_function;;
open Whayrf_constraint_closure_non_function;;
open Whayrf_logger;;
open Whayrf_types_pretty;;

let logger = make_logger "Whayrf_constraint_closure_full";;

(** Full constraint closure (no superscript) *)
let rec full_closure dependency_graph constraint_set =
  logger `trace
    (sprintf
       "`full_closure' called with `constraint_set' = `%s'."
       (pretty_constraint_set constraint_set)
    )
  ;
  closure_fixpoint
    [
      (* The order _is relevant_ for the correct behavior of the program.

         On function closure we perform a subordinate closure. And we don't want
         the subordinate closure doing non-function closure steps that the main
         closure should have done.

         The solution is to only enter function closure steps after finishing the
         non-function closure.

         This is a slight divergence on the presentation on the paper, but for a
         good reason: it eliminates repetition of work and increases performance. *)
      non_function_closure;
      function_closure (full_closure dependency_graph) dependency_graph
    ]
    constraint_set
;;

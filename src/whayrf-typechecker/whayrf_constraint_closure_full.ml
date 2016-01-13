open Batteries;;

open Whayrf_constraint_closure_fixpoint;;
open Whayrf_constraint_closure_function;;
open Whayrf_constraint_closure_non_function;;

(** Full constraint closure (no superscript) *)
let full_closure dependency_graph =
  closure_fixpoint
    [
      (* The order in which operations happen here is fundamental for the correct
         behavior of the program.

         This is because, on function closure, we perform a subordinate closure. And
         we don't want the subordinate closure doing non-function closure steps that
         the main closure should have done.

         The solution is to only enter function closure steps after finishing the
         non-function closure.

         This is a slight divergence on the presentation on the paper, but for a
         good reason: it eliminates repetition of work and increases performance. *)
      non_function_closure;
      function_closure dependency_graph
    ]
;;

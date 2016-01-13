open Batteries;;

open Whayrf_constraint_closure_fixpoint;;
open Whayrf_constraint_closure_non_function;;
open Whayrf_constraint_closure_ordering_function;;

(** Ordering-function constraint closure (O superscript) *)
let ordering_closure =
  closure_fixpoint
    [
      (* The order _is relevant_ for the correctness of the program. *)
      non_function_closure;
      ordering_function_closure
    ]
;;

open Batteries;;
open Printf;;

open Whayrf_ast;;
open Whayrf_ast_pretty;;
open Whayrf_consistency;;
open Whayrf_constraint_closure_fixpoint;;
open Whayrf_constraint_closure_non_function;;
open Whayrf_dependency_resolution;;
open Whayrf_function_pattern_search;;
open Whayrf_initial_alignment;;
open Whayrf_logger;;
open Whayrf_notation;;
open Whayrf_pattern_subsumption;;
open Whayrf_type_compatibility;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_types_utils;;
open Whayrf_utils;;

let logger = make_logger "Whayrf_constraint_closure_function";;

(* CHECK *)
let check
    full_closure
    dependency_graph
    (
      Function_type (
        parameter_type_variable,
        Constrained_type (
          return_type_variable,
          body_constraint_set
        )
      )
    )
    constraint_set
    pattern =
  match pattern with
  | Function_pattern (
      parameter_pattern,
      return_pattern
    ) ->
    let additional_constraints_to_test = Constraint_set.of_enum @@ List.enum [
        Lower_bound_constraint (
          Restricted_type_lower_bound (
            Restricted_type (
              Unknown_type,
              Type_restriction (
                Positive_pattern_set (
                  Pattern_set.singleton parameter_pattern
                ),
                Negative_pattern_set (Pattern_set.empty)
              )
            )
          ),
          parameter_type_variable
        );
        Type_variable_constraint (
          return_type_variable,
          return_pattern
        )
      ]
    in
    let constraint_set_to_test =
      List.fold_left
        Constraint_set.union
        Constraint_set.empty
        [
          constraint_set;
          body_constraint_set;
          additional_constraints_to_test
        ]
    in
    logger `trace ("Performing subordinate closure with constraint set: " ^ pretty_constraint_set constraint_set_to_test);
    let closed_constraint_set_to_test =
      full_closure dependency_graph constraint_set_to_test
    in
    is_consistent closed_constraint_set_to_test

  | _ ->
    raise @@ Invariant_failure "`check' called with non-function pattern."
;;

(** READY *)
let ready function_pattern_matching_case dependency_graph constraint_set =
  dependencies function_pattern_matching_case dependency_graph
  |> Function_pattern_matching_case_set.for_all
    (
      fun (
        Function_pattern_matching_case (
          function_type,
          pattern
        )
      ) ->
        (
          Constraint_set.mem
            (
              Function_pattern_matching_constraint (
                Function_pattern_matching_constraint_positive (
                  function_type,
                  pattern
                )
              )
            )
            constraint_set
        ) ||
        (
          Constraint_set.mem
            (
              Function_pattern_matching_constraint (
                Function_pattern_matching_constraint_negative (
                  function_type,
                  pattern
                )
              )
            )
            constraint_set
        )
    )
;;

(** FUNCTION CLOSURE from the appendix and FUNCTION MATCH and FUNCTION
    ANTI-MATCH from the main paper submission *)
let close_by_function_closure full_closure dependency_graph constraint_set =
  logger `trace
    (sprintf
       "`function_closure' called with `constraint_set' = `%s'."
       (pretty_constraint_set constraint_set)
    )
  ;
  (* Look for function_type-pattern pairs, as per Function Closure Rules in the
     main paper. *)
  let function_pattern_matching_cases =
    function_pattern_search constraint_set
  in
  function_pattern_matching_cases
  |> Function_pattern_matching_case_set.enum
  |> Enum.filter_map
    (
      fun (
        (
          Function_pattern_matching_case (
            function_type,
            pattern
          )
        ) as function_pattern_matching_case
      ) ->
        (* Skip over squelch constraints and the function_type-pattern pairs
           that are not READY (i.e., their dependencies are not resolved). *)
        if (
          Constraint_set.mem
            (
              Function_pattern_matching_constraint (
                Function_pattern_matching_constraint_squelch (
                  function_type,
                  pattern
                )
              )
            )
            constraint_set
        ) || (not
                (ready function_pattern_matching_case dependency_graph constraint_set)
             )
        then
          None
        else
          Some (
            (* Call CHECK, as per FUNCTION CLOSURE in the appendix. CHECK in the
               appendix and FUN MATCH in the main paper are similar, except that
               CHECK expects squelches to already be in the constraint set,
               while FUN MATCH adds them itself.

               CHECK is preferable, in this case, because the function pattern
               matching cases are already calculated at this point. *)
            let squelch_constraints =
              function_pattern_matching_cases
              |> Function_pattern_matching_case_set.enum
              |> Enum.map
                (
                  fun (
                    Function_pattern_matching_case (
                      function_type,
                      pattern
                    )
                  ) ->
                    Function_pattern_matching_constraint (
                      Function_pattern_matching_constraint_squelch (
                        function_type, pattern
                      )
                    )
                )
              |> Constraint_set.of_enum
            in
            if (
              check
                full_closure
                dependency_graph
                function_type
                (
                  Constraint_set.union
                    constraint_set
                    squelch_constraints
                )
                pattern
            )
            (* Generate positive and negative mach constraints, as per Function
               Closure Rules in the main paper and FUNCTION CLOSURE in the appendix. *)
            then
              Function_pattern_matching_constraint (
                Function_pattern_matching_constraint_positive (
                  function_type,
                  pattern
                )
              )
            else
              Function_pattern_matching_constraint (
                Function_pattern_matching_constraint_negative (
                  function_type,
                  pattern
                )
              )
          )
    )
  |> Constraint_set.of_enum
  |> Constraint_set.union constraint_set
;;

(** CYCLE BREAKER *)
let close_by_cycle_breaker dependency_graph constraint_set =
  function_pattern_matching_cases_participating_in_cycles dependency_graph
  |> Function_pattern_matching_case_set.enum
  |> Enum.map
    (
      fun (
        Function_pattern_matching_case (
          function_type,
          pattern
        )
      ) ->
        Function_pattern_matching_constraint (
          Function_pattern_matching_constraint_positive (
            function_type,
            pattern
          )
        )
    )
  |> Constraint_set.of_enum
  |> Constraint_set.union constraint_set
;;

(** Function constraint closure (F superscript)

    A hybrid from Function Closure Rules in the main paper and FUNCTION CLOSURE
    in the appendix. *)
let function_closure full_closure dependency_graph constraint_set =
  constraint_set
  |> close_by_cycle_breaker dependency_graph
  |> closure_fixpoint [close_by_function_closure full_closure dependency_graph]
;;

open Batteries;;

open Whayrf_ast;;
open Whayrf_ast_pretty;;
open Whayrf_consistency;;
open Whayrf_constraint_closure_non_function;;
open Whayrf_function_pattern_search;;
open Whayrf_initial_alignment;;
open Whayrf_logger;;
open Whayrf_notation;;
open Whayrf_pattern_subsumption;;
open Whayrf_type_compatibility;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

let logger = make_logger "Whayrf_constraint_closure_function";;

(** Perform Function Constraint Closure (i.e. the one with the F superscript).

    This function doesn't perform a single step, but the fixpoint (omega). This
    returns the augmented constraint set with the new constraints as well as the
    original constraints. *)
let perform_function_closure perform_closure constraint_set =
  let augmented_constraint_set =
    constraint_set
    |> Constraint_set.enum
    |> Enum.filter_map
      (
        fun tconstraint ->
          match tconstraint with
          (* FUNCTION CLOSURE *)
          | Lower_bound_constraint (
              Conditional_lower_bound (
                type_variable,
                pattern,
                _,
                _
              ),
              _
            )

          (* FUNCTION CLOSURE (UPPER BOUNDING PATTERN) *)
          | Type_variable_constraint (
              type_variable,
              pattern
            ) ->
            Some (
              function_pattern_search_type_variable
                type_variable
                constraint_set
                pattern
              |> Function_pattern_matching_case_set.enum
              |> Enum.map
                (
                  fun (
                    Function_pattern_matching_case (
                      (
                        Function_type (
                          parameter_type_variable,
                          Constrained_type (
                            return_type_variable,
                            body_constraint_set
                          )
                        )
                      ) as function_type,
                      pattern
                    )
                  ) ->
                    if not (
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
                      ) then
                      match pattern with
                      (* FUNCTION MATCH and FUNCTION ANTI-MATCH *)
                      (* These rules are almost identical, so they share most of the code. The only
                         difference is in the kind of constraint that is generated, based on the
                         consistency of the resulting constraint closure. *)
                      | Function_pattern (
                          parameter_pattern,
                          return_pattern
                        ) ->
                        let squelch_constraints =
                          function_pattern_search constraint_set
                          |> Function_pattern_matching_case_set.enum
                          |> Enum.map
                            (
                              fun (Function_pattern_matching_case (function_type, pattern)) ->
                                Function_pattern_matching_constraint (
                                  Function_pattern_matching_constraint_squelch (
                                    function_type, pattern
                                  )
                                )
                            )
                          |> Constraint_set.of_enum
                        in
                        logger `trace ("Generated squelch constraints: `" ^ pretty_constraint_set squelch_constraints ^ "'.");

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
                              additional_constraints_to_test;
                              squelch_constraints
                            ]
                        in
                        logger `trace ("The constraint set being close over for function pattern search is: " ^ pretty_constraint_set constraint_set_to_test);
                        let closed_constraint_set_to_test =
                          perform_closure constraint_set_to_test
                        in
                        let is_consistent_constraint_set_to_test =
                          is_consistent closed_constraint_set_to_test
                        in
                        let new_constraint =
                          Function_pattern_matching_constraint (
                            if is_consistent_constraint_set_to_test then
                              Function_pattern_matching_constraint_positive (
                                function_type,
                                pattern
                              )
                            else
                              Function_pattern_matching_constraint_negative (
                                function_type,
                                pattern
                              )
                          )
                        in
                        Constraint_set.singleton (new_constraint)

                      | _ -> raise @@ Invariant_failure "Shouldn't consider function pattern matching case that's not either function or forall."

                    else
                      Constraint_set.empty
                )
              |> Enum.fold Constraint_set.union Constraint_set.empty
            )
          | _ -> None
      )
    |> Enum.fold Constraint_set.union constraint_set
  in
  logger `trace ("New constraints generated by function constraint closure: `" ^ pretty_constraint_set (Constraint_set.diff augmented_constraint_set constraint_set) ^ "'.");
  augmented_constraint_set
;;

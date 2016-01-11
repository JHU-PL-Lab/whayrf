open Batteries;;

open Whayrf_ast;;
open Whayrf_consistency;;
open Whayrf_initial_alignment;;
open Whayrf_notation;;
open Whayrf_pattern_subsumption;;
open Whayrf_type_compatibility;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

(** Perform Ordering Inference Constraint Closure (i.e. the one with the OF
    superscript).

    Most of these functions don't perform a single step, but the fixpoint. They
    only return the new constraints that can be added to the constraint set, not
    the already augmented constraint set. This makes it easier to determine when
    there are no more steps to take (i.e. the closure is finished). *)

(** FUNCTION PATTERN SIMULATED CALL *)
let close_by_function_pattern_simulated_call constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint(
            Conditional_lower_bound (
              subject_type_variable,
              Function_pattern (
                parameter_pattern,
                return_pattern
              ),
              _,
              _
            ),
            _
          ) ->
          Some (
            constraint_set
            |> Constraint_set.enum
            |> Enum.filter_map
              (
                fun tconstraint ->
                  match tconstraint with
                  | Lower_bound_constraint(
                      Restricted_type_lower_bound (
                        Restricted_type (
                          Function_type_type (
                            Function_type (
                              parameter_type_variable,
                              Constrained_type (
                                return_type_variable,
                                body_constraint_set
                              )
                            )
                          ),
                          _
                        )
                      ),
                      other_subject_type_variable
                    ) ->
                    if subject_type_variable = other_subject_type_variable then
                      Some (
                        Enum.append
                          (Constraint_set.enum body_constraint_set)
                          (
                            List.enum [
                              Lower_bound_constraint (
                                Restricted_type_lower_bound (
                                  Restricted_type (
                                    Unknown_type,
                                    Type_restriction (
                                      Positive_pattern_set (
                                        Pattern_set.singleton parameter_pattern
                                      ),
                                      Negative_pattern_set (
                                        Pattern_set.empty
                                      )
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
                          )
                      )
                    else
                      None
                  | _ -> None
              )
            |> Enum.concat
          )
        | _ -> None
    )
  |> Enum.concat
  |> Constraint_set.of_enum
;;

(** FUNCTION PATTERN SIMULATED SUCCESS *)
let close_by_function_simulated_success constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint(
            Conditional_lower_bound (
              subject_type_variable,
              (
                Function_pattern (
                  _,
                  _
                ) as function_pattern
              ),
              _,
              _
            ),
            _
          ) ->
          Some (
            constraint_set
            |> Constraint_set.enum
            |> Enum.filter_map
              (
                fun tconstraint ->
                  match tconstraint with
                  | Lower_bound_constraint(
                      Restricted_type_lower_bound (
                        Restricted_type (
                          Function_type_type (
                            function_type
                          ),
                          type_restriction
                        )
                      ),
                      other_subject_type_variable
                    ) ->
                    if (subject_type_variable = other_subject_type_variable) &&
                       (
                         Whayrf_type_compatibility.is_compatible_restricted_type
                           (
                             Restricted_type (
                               Unknown_type,
                               type_restriction
                             )
                           )
                           constraint_set
                           (
                             Type_restriction (
                               Positive_pattern_set (
                                 Pattern_set.singleton function_pattern
                               ),
                               Negative_pattern_set (
                                 Pattern_set.empty
                               )
                             )
                           )
                       )
                    then
                      Some (
                        Function_pattern_matching_constraint (
                          Function_pattern_matching_constraint_positive (
                            function_type,
                            function_pattern
                          )
                        )
                      )
                    else
                      None
                  | _ -> None
              )
          )
        | _ -> None
    )
  |> Enum.concat
  |> Constraint_set.of_enum
;;

(** FUNCTION PATTERN SIMULATED FAILURE *)
let close_by_function_simulated_failure constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint(
            Conditional_lower_bound (
              subject_type_variable,
              (
                Function_pattern (
                  _,
                  _
                ) as function_pattern
              ),
              _,
              _
            ),
            _
          ) ->
          Some (
            constraint_set
            |> Constraint_set.enum
            |> Enum.filter_map
              (
                fun tconstraint ->
                  match tconstraint with
                  | Lower_bound_constraint(
                      Restricted_type_lower_bound (
                        Restricted_type (
                          Function_type_type (
                            function_type
                          ),
                          type_restriction
                        )
                      ),
                      other_subject_type_variable
                    ) ->
                    if (subject_type_variable = other_subject_type_variable) &&
                       (
                         Whayrf_type_compatibility.is_compatible_restricted_type
                           (
                             Restricted_type (
                               Unknown_type,
                               type_restriction
                             )
                           )
                           constraint_set
                           (
                             Type_restriction (
                               Positive_pattern_set (
                                 Pattern_set.empty
                               ),
                               Negative_pattern_set (
                                 Pattern_set.singleton function_pattern
                               )
                             )
                           )
                       )
                    then
                      Some (
                        Function_pattern_matching_constraint (
                          Function_pattern_matching_constraint_negative (
                            function_type,
                            function_pattern
                          )
                        )
                      )
                    else
                      None
                  | _ -> None
              )
          )
        | _ -> None
    )
  |> Enum.concat
  |> Constraint_set.of_enum
;;

(** Entry point for Ordering Inference Constraint Closure. Perform closure rules
    until fixpoint (omega) is reached. This returns the augmented constraint set
    with the new constraints as well as the original constraints. *)
let rec perform_ordering_inference_closure perform_closure constraint_set =
  (* The order in which operations happen here is irrelevant for the correct
       behavior of the program. *)
  let closure_functions =
    [
      close_by_function_pattern_simulated_call;
      close_by_function_simulated_success;
      close_by_function_simulated_failure
    ]
  in
  let augmented_constraint_set =
    List.fold_left
      (
        fun partially_augmented_constraint_set closure_function ->
          let inferred_constraints = closure_function partially_augmented_constraint_set in
          Constraint_set.union partially_augmented_constraint_set inferred_constraints
      )
      constraint_set
      closure_functions
  in
  if (Enum.count (Constraint_set.enum constraint_set)) <>
     (Enum.count (Constraint_set.enum augmented_constraint_set)) then
    perform_ordering_inference_closure perform_closure augmented_constraint_set
  else
    augmented_constraint_set
;;

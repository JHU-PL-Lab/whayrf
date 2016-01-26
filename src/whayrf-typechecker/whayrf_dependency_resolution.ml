open Batteries;;

open Whayrf_ast;;
open Whayrf_function_pattern_search;;
open Whayrf_type_compatibility;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_types_utils;;
open Whayrf_utils;;

(** Affection is a concept necessary to implement the dependency graph
    resolution. It records the fact that `a -affects-> b'. A closure is
    performed on the `<<C' rules to build an `affection_set'. From the
    `affection_set' the dependency graph is devised. *)
type affection =
  | Type_variable_type_variable_affection of type_variable * type_variable
  | Type_variable_function_pattern_matching_case_affection of type_variable * function_pattern_matching_case
  | Function_pattern_matching_case_type_variable_affection of function_pattern_matching_case * type_variable
;;

module Affection_order =
struct
  type t = affection
  let compare = compare
end
;;
module Affection_set = Set.Make(Affection_order);;

(** VARIABLE *)
let close_by_variable affection_set constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Type_variable_lower_bound (
              type_variable_before
            ),
            type_variable_after
          )
          ->
          Some (
            Type_variable_type_variable_affection (
              type_variable_before,
              type_variable_after
            )
          )

        | _ -> None
    )
  |> Affection_set.of_enum
  |> Affection_set.union affection_set
;;

(** REFLEXIVITY *)
let close_by_reflexivity affection_set constraint_set =
  type_variables_in constraint_set
  |> Type_variable_set.enum
  |> Enum.map
    (
      fun type_variable ->
        Type_variable_type_variable_affection (
          type_variable,
          type_variable
        )
    )
  |> Affection_set.of_enum
  |> Affection_set.union affection_set
;;

(** TRANSITIVITY *)
let close_by_transitivity affection_set constraint_set =
  affection_set
  |> Affection_set.enum
  |> Enum.filter_map
    (
      fun affection_1 ->
        match affection_1 with
        | Type_variable_type_variable_affection (
            type_variable_before,
            type_variable_intermediary
          ) ->
          Some (
            affection_set
            |> Affection_set.enum
            |> Enum.filter_map
              (
                fun affection_2 ->
                  match affection_2 with
                  | Type_variable_type_variable_affection (
                      other_type_variable_intermediary,
                      type_variable_after
                    ) ->
                    if type_variable_intermediary = other_type_variable_intermediary then
                      Some (
                        Type_variable_type_variable_affection (
                          type_variable_before,
                          type_variable_after
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
  |> Affection_set.of_enum
  |> Affection_set.union affection_set
;;

(** APPLICATION *)
let close_by_application affection_set constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Application_lower_bound (
              type_variable_function,
              type_variable_parameter
            ),
            type_variable_application_result
          ) ->
          Some (
            Affection_set.of_list [
              Type_variable_type_variable_affection (
                type_variable_function,
                type_variable_application_result
              );
              Type_variable_type_variable_affection (
                type_variable_parameter,
                type_variable_application_result
              )
            ]
          )

        | _ -> None
    )
  |> Enum.fold Affection_set.union affection_set
;;

(** PATTERN-MATCHING *)
let close_by_pattern_matching affection_set constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Type_variable_constraint (
            subject,
            pattern
          ) ->
          Some (
            constraint_set
            |> Constraint_set.enum
            |> Enum.filter_map
              (
                fun tconstraint ->
                  match tconstraint with
                  | Lower_bound_constraint (
                      Restricted_type_lower_bound (
                        Restricted_type (
                          Function_type_type (
                            (
                              Function_type (
                                _,
                                Constrained_type (
                                  _,
                                  body_constraint_set
                                )
                              )
                            )
                            as function_type
                          ),
                          _
                        )
                      ),
                      other_subject
                    ) ->
                    if subject = other_subject then
                      Some (
                        body_constraint_set
                        |> Constraint_set.enum
                        |> Enum.filter_map
                          (
                            fun tconstraint ->
                              match tconstraint with
                              | Lower_bound_constraint (
                                  _,
                                  type_variable_before
                                ) ->
                                Some (
                                  Type_variable_function_pattern_matching_case_affection (
                                    type_variable_before,
                                    Function_pattern_matching_case (
                                      function_type,
                                      pattern
                                    )
                                  )
                                )

                              | _ -> None
                          )
                        |> Affection_set.of_enum
                      )
                    else
                      None

                  | _ -> None
              )
            |> Enum.fold Affection_set.union Affection_set.empty
          )
        | _ -> None
    )
  |> Enum.fold Affection_set.union affection_set
;;

(** CONDITIONAL INPUT *)
let close_by_conditional_input affection_set constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Conditional_lower_bound (
              subject,
              pattern,
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
                  | Lower_bound_constraint (
                      Restricted_type_lower_bound (
                        Restricted_type (
                          Function_type_type (
                            (
                              Function_type (
                                _,
                                Constrained_type (
                                  _,
                                  body_constraint_set
                                )
                              )
                            )
                            as function_type
                          ),
                          _
                        )
                      ),
                      other_subject
                    ) ->
                    if subject = other_subject then
                      Some (
                        body_constraint_set
                        |> Constraint_set.enum
                        |> Enum.filter_map
                          (
                            fun tconstraint ->
                              match tconstraint with
                              | Lower_bound_constraint (
                                  _,
                                  type_variable_before
                                ) ->
                                Some (
                                  Type_variable_function_pattern_matching_case_affection (
                                    type_variable_before,
                                    Function_pattern_matching_case (
                                      function_type,
                                      pattern
                                    )
                                  )
                                )

                              | _ -> None
                          )
                        |> Affection_set.of_enum
                      )
                    else
                      None

                  | _ -> None
              )
            |> Enum.fold Affection_set.union Affection_set.empty
          )
        | _ -> None
    )
  |> Enum.fold Affection_set.union affection_set
;;

(** CONDITIONAL OUTPUT *)
let close_by_conditional_output affection_set constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Conditional_lower_bound (
              subject,
              pattern,
              _,
              _
            ),
            conditional_output_type_variable
          ) ->
          Some (
            constraint_set
            |> Constraint_set.enum
            |> Enum.filter_map
              (
                fun tconstraint ->
                  match tconstraint with
                  | Lower_bound_constraint (
                      Restricted_type_lower_bound (
                        Restricted_type (
                          Function_type_type (
                            function_type
                          ),
                          _
                        )
                      ),
                      other_subject
                    ) ->
                    if subject = other_subject then
                      Some (
                        Function_pattern_matching_case_type_variable_affection (
                          Function_pattern_matching_case (
                            function_type,
                            pattern
                          ),
                          conditional_output_type_variable
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
  |> Affection_set.of_enum
  |> Affection_set.union affection_set
;;

(** CONDITIONAL SUCCESS BODY *)
let close_by_conditional_success_body affection_set constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Conditional_lower_bound (
              subject,
              pattern,
              Function_type (
                _,
                Constrained_type (
                  _,
                  body_constraint_set
                )
              ),
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
                  | Lower_bound_constraint (
                      Restricted_type_lower_bound (
                        (
                          Restricted_type (
                            Function_type_type (
                              function_type
                            ),
                            _
                          )
                        ) as restricted_type
                      ),
                      other_subject
                    ) ->
                    if (
                      subject = other_subject
                    ) && (
                        is_compatible_restricted_type
                          restricted_type
                          constraint_set
                          (
                            Type_restriction (
                              Positive_pattern_set (
                                Pattern_set.singleton pattern
                              ),
                              Negative_pattern_set (
                                Pattern_set.empty
                              )
                            )
                          )
                      ) then
                      Some (
                        body_constraint_set
                        |> Constraint_set.enum
                        |> Enum.filter_map
                          (
                            fun tconstraint ->
                              match tconstraint with
                              | Lower_bound_constraint (
                                  _,
                                  type_variable_after
                                ) ->
                                Some (
                                  Function_pattern_matching_case_type_variable_affection (
                                    Function_pattern_matching_case (
                                      function_type,
                                      pattern
                                    ),
                                    type_variable_after
                                  )
                                )

                              | _ -> None
                          )
                        |> Affection_set.of_enum
                      )
                    else
                      None

                  | _ -> None
              )
          )
        | _ -> None
    )
  |> Enum.concat
  |> Enum.fold Affection_set.union affection_set
;;

(** CONDITIONAL FAILURE BODY *)
let close_by_conditional_failure_body affection_set constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Conditional_lower_bound (
              subject,
              pattern,
              _,
              Function_type (
                _,
                Constrained_type (
                  _,
                  body_constraint_set
                )
              )
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
                  | Lower_bound_constraint (
                      Restricted_type_lower_bound (
                        (
                          Restricted_type (
                            Function_type_type (
                              function_type
                            ),
                            _
                          )
                        ) as restricted_type
                      ),
                      other_subject
                    ) ->
                    if (
                      subject = other_subject
                    ) && (
                        is_compatible_restricted_type
                          restricted_type
                          constraint_set
                          (
                            Type_restriction (
                              Positive_pattern_set (
                                Pattern_set.empty
                              ),
                              Negative_pattern_set (
                                Pattern_set.singleton pattern
                              )
                            )
                          )
                      ) then
                      Some (
                        body_constraint_set
                        |> Constraint_set.enum
                        |> Enum.filter_map
                          (
                            fun tconstraint ->
                              match tconstraint with
                              | Lower_bound_constraint (
                                  _,
                                  type_variable_after
                                ) ->
                                Some (
                                  Function_pattern_matching_case_type_variable_affection (
                                    Function_pattern_matching_case (
                                      function_type,
                                      pattern
                                    ),
                                    type_variable_after
                                  )
                                )

                              | _ -> None
                          )
                        |> Affection_set.of_enum
                      )
                    else
                      None

                  | _ -> None
              )
          )
        | _ -> None
    )
  |> Enum.concat
  |> Enum.fold Affection_set.union affection_set
;;

(** RECORD *)
let close_by_record affection_set constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Restricted_type_lower_bound (
              Restricted_type (
                Record_type (
                  record_elements
                ),
                _
              )
            ),
            type_variable_record
          ) ->
          Some (
            record_elements
            |> Ident_map.enum
            |> Enum.map
              (
                fun (
                  _,
                  type_variable_element
                ) ->
                  Type_variable_type_variable_affection (
                    type_variable_element,
                    type_variable_record
                  )
              )
            |> Affection_set.of_enum
          )

        | _ -> None
    )
  |> Enum.fold Affection_set.union affection_set
;;

(** Run a list of affection closure rules to a fixpoint. *)
let rec affection_closure_fixpoint rules affection_set constraint_set =
  let augmented_affection_set =
    List.fold_left
      (
        fun affection_set rule ->
          rule affection_set constraint_set
      )
      affection_set
      rules
  in
  if Affection_set.equal affection_set augmented_affection_set then
    affection_set
  else
    affection_closure_fixpoint rules augmented_affection_set constraint_set
;;

let affection_closure constraint_set =
  affection_closure_fixpoint
    [
      (* The order is irrelevant for the correctness of the program. *)
      close_by_variable;
      close_by_reflexivity;
      close_by_transitivity;
      close_by_application;
      close_by_pattern_matching;
      close_by_conditional_input;
      close_by_conditional_output;
      close_by_conditional_success_body;
      close_by_conditional_failure_body;
      close_by_record
    ]
    Affection_set.empty
    constraint_set
;;

(** ≺C *)
let is_dependency
    potential_dependency_function_pattern_matching_case
    dependent_function_pattern_matching_case
    affections
    constraint_set =
  let type_variables_in_constraint_set =
    type_variables_in constraint_set
  in
  type_variables_in_constraint_set
  |> Type_variable_set.enum
  |> Enum.exists
    (
      fun type_variable_1 ->
        type_variables_in_constraint_set
        |> Type_variable_set.enum
        |> Enum.exists
          (
            fun type_variable_2 ->
              List.enum [
                Function_pattern_matching_case_type_variable_affection (
                  potential_dependency_function_pattern_matching_case,
                  type_variable_1
                );
                Type_variable_type_variable_affection (
                  type_variable_1,
                  type_variable_2
                );
                Type_variable_function_pattern_matching_case_affection (
                  type_variable_2,
                  dependent_function_pattern_matching_case
                )
              ]
              |> Enum.for_all
                (
                  fun requirement ->
                    Affection_set.mem
                      requirement
                      affections
                )
          )
    )
;;

let dependency_resolution constraint_set =
  Dependency_graph (
    let function_pattern_matching_cases =
      function_pattern_search constraint_set
    in
    let affections =
      affection_closure constraint_set
    in
    function_pattern_matching_cases
    |> Function_pattern_matching_case_set.enum
    |> Enum.map
      (
        fun dependent_function_pattern_matching_case ->
          (
            dependent_function_pattern_matching_case,
            function_pattern_matching_cases
            |> Function_pattern_matching_case_set.enum
            |> Enum.filter
              (
                fun potential_dependency_function_pattern_matching_case ->
                  is_dependency
                    potential_dependency_function_pattern_matching_case
                    dependent_function_pattern_matching_case
                    affections
                    constraint_set
              )
            |> Function_pattern_matching_case_set.of_enum
          )
      )
    |> Function_pattern_matching_case_map.of_enum
  )
;;

(** Inspired by BLOCKING and CYCLE BREAKER from the main paper submission. *)
let function_pattern_matching_cases_participating_in_cycles (
    Dependency_graph (
      dependency_elements
    )
  ) =
  let rec is_in_cycle
      subject_function_pattern_matching_case
      current_function_pattern_matching_case
      trail =
    (* Visiting the same subject again, i.e. found a cycle. *)
    if (
      not (
        Function_pattern_matching_case_set.equal
          trail
          Function_pattern_matching_case_set.empty
      )
    ) && (
        subject_function_pattern_matching_case =
        current_function_pattern_matching_case
      )
    then
      true
    else
      (* A cycle was found, but the current not doesn't participate in it.

         Think of the case of A in the following graph:

         A -> B -> C
              ^    |
              ------
      *)
      if Function_pattern_matching_case_set.mem
        current_function_pattern_matching_case
        trail
      then
        false
      else
        let function_pattern_matching_case_dependencies =
          Function_pattern_matching_case_map.find
            current_function_pattern_matching_case
            dependency_elements
        in
        function_pattern_matching_case_dependencies
        |> Function_pattern_matching_case_set.enum
        |> Enum.exists
          (
            fun current_function_pattern_matching_case_set_dependency ->
              is_in_cycle
                subject_function_pattern_matching_case
                current_function_pattern_matching_case_set_dependency
                (
                  Function_pattern_matching_case_set.add
                    current_function_pattern_matching_case
                    trail
                )
          )
  in
  dependency_elements
  |> Function_pattern_matching_case_map.keys
  |> Enum.filter
    (
      fun function_pattern_matching_case ->
        is_in_cycle
          function_pattern_matching_case
          function_pattern_matching_case
          Function_pattern_matching_case_set.empty
    )
  |> Function_pattern_matching_case_set.of_enum
;;

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

(** Perform Non-Function Constraint Closure (i.e. the one with the N
    superscript).

    Most of these functions don't perform a single step, but the fixpoint. They
    only return the new constraints that can be added to the constraint set, not
    the already augmented constraint set. This makes it easier to determine when
    there are no more steps to take (i.e. the closure is finished). *)

(** TRANSITIVITY *)
let close_by_transitivity constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint(
            Restricted_type_lower_bound(restricted_type),
            intermediate_type_variable
          ) ->
          Some (
            constraint_set
            |> Constraint_set.enum
            |> Enum.filter_map
              (
                fun tconstraint ->
                  match tconstraint with
                  | Lower_bound_constraint(
                      Type_variable_lower_bound(other_intermediate_type_variable),
                      final_type_variable
                    ) ->
                    if intermediate_type_variable = other_intermediate_type_variable then
                      Some (
                        Lower_bound_constraint(
                          Restricted_type_lower_bound(restricted_type),
                          final_type_variable
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

(** PROJECTION *)
let close_by_projection constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Projection_lower_bound (
              record_type_variable,
              label
            ),
            projected_type_variable
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
                          Record_type (record_elements),
                          Type_restriction (
                            Positive_pattern_set (positive_patterns),
                            Negative_pattern_set (negative_patterns)
                          )
                        )
                      ),
                      other_record_type_variable
                    ) ->
                    if (
                      (record_type_variable = other_record_type_variable) &&
                      (Ident_map.mem label record_elements)
                    ) then
                      let label_type_variable = Ident_map.find label record_elements in
                      let projected_patterns = project_pattern_set label positive_patterns in
                      Some (
                        constraint_set
                        |> Constraint_set.enum
                        |> Enum.filter_map
                          (
                            fun tconstraint ->
                              match tconstraint with
                              | Lower_bound_constraint (
                                  Restricted_type_lower_bound (
                                    Restricted_type(
                                      ttype,
                                      _
                                    ) as restricted_type
                                  ),
                                  other_label_type_variable
                                ) ->
                                if (
                                  (label_type_variable = other_label_type_variable) &&
                                  (is_compatible_restricted_type
                                     restricted_type
                                     constraint_set
                                     (
                                       Type_restriction (
                                         Positive_pattern_set (projected_patterns),
                                         Negative_pattern_set (Pattern_set.empty)
                                       )
                                     )
                                  )
                                ) then
                                  Some (
                                    Lower_bound_constraint (
                                      Restricted_type_lower_bound (
                                        Restricted_type (
                                          ttype,
                                          Type_restriction (
                                            Positive_pattern_set (
                                              (* On the Figure, note that `\tau'
                                                 is a restricted type
                                                 already. The Figure Notation
                                                 says, in that case, we should
                                                 union the patterns in the
                                                 filter together. *)
                                              Pattern_set.union
                                                positive_patterns
                                                projected_patterns
                                            ),
                                            Negative_pattern_set (negative_patterns)
                                          )
                                        )
                                      ),
                                      projected_type_variable
                                    )
                                  )
                                else
                                  None
                              | _ -> None
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

(** APPLICATION *)
let close_by_application constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map (
    fun tconstraint ->
      match tconstraint with
      | Lower_bound_constraint (
          Application_lower_bound (
            function_type_variable,
            actual_parameter_type_variable
          ),
          function_return_type_variable
        ) ->
        Some (
          constraint_set
          |> Constraint_set.enum
          |> Enum.filter_map (
            fun tconstraint ->
              match tconstraint with
              | Lower_bound_constraint (
                  Restricted_type_lower_bound (
                    Restricted_type (
                      Function_type_type (
                        Function_type (
                          formal_parameter_type_variable,
                          Constrained_type (
                            body_type_variable,
                            body_constraint_set
                          )
                        )
                      ),
                      _
                    )
                  ),
                  other_function_type_variable
                ) ->
                if (function_type_variable = other_function_type_variable) then
                  Some (
                    constraint_set
                    |> Constraint_set.enum
                    |> Enum.filter_map (
                      fun tconstraint ->
                        match tconstraint with
                        | Lower_bound_constraint (
                            actual_parameter_lower_bound,
                            other_actual_parameter_type_variable
                          ) ->
                          if (actual_parameter_type_variable = other_actual_parameter_type_variable) then
                            Some (
                              Enum.append
                                (Constraint_set.enum body_constraint_set)
                                (
                                  List.enum [
                                    Lower_bound_constraint (
                                      actual_parameter_lower_bound,
                                      formal_parameter_type_variable
                                    );
                                    Lower_bound_constraint (
                                      Type_variable_lower_bound (
                                        body_type_variable
                                      ),
                                      function_return_type_variable
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

(** CONDITIONAL SUCCESS *)
let close_by_conditional_success constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map (
    fun tconstraint ->
      match tconstraint with
      | Lower_bound_constraint (
          Conditional_lower_bound (
            subject_type_variable,
            pattern,
            Function_type (
              parameter_type_variable,
              Constrained_type (
                body_type_variable,
                body_constraint_set
              )
            ),
            _
          ),
          conditional_result_type_variable
        ) ->
        Some (
          constraint_set
          |> Constraint_set.enum
          |> Enum.filter_map (
            fun tconstraint ->
              match tconstraint with
              | Lower_bound_constraint (
                  Restricted_type_lower_bound (
                    Restricted_type (
                      ttype,
                      Type_restriction (
                        Positive_pattern_set (positive_patterns),
                        Negative_pattern_set (negative_patterns)
                      )
                    ) as restricted_type
                  ),
                  other_subject_type_variable
                ) ->
                if (
                  (subject_type_variable = other_subject_type_variable) &&
                  (
                    is_compatible_restricted_type
                      restricted_type
                      constraint_set
                      (
                        Type_restriction
                          (
                            Positive_pattern_set (
                              Pattern_set.add
                                pattern
                                Pattern_set.empty
                            ),
                            Negative_pattern_set Pattern_set.empty
                          )
                      )
                  )
                ) then
                  Some (
                    Enum.append
                      (Constraint_set.enum body_constraint_set)
                      (
                        List.enum [
                          Lower_bound_constraint (
                            Restricted_type_lower_bound (
                              Restricted_type (
                                ttype,
                                Type_restriction (
                                  Positive_pattern_set (
                                    (* On the Figure, note that `\tau' is a
                                       restricted type already. The Figure
                                       Notation says, in that case, we should
                                       union the patterns in the filter
                                       together. *)
                                    Pattern_set.add
                                      pattern
                                      positive_patterns
                                  ),
                                  Negative_pattern_set (
                                    negative_patterns
                                  )
                                )
                              )
                            ),
                            parameter_type_variable
                          );
                          Lower_bound_constraint (
                            Type_variable_lower_bound (
                              body_type_variable
                            ),
                            conditional_result_type_variable
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

(** CONDITIONAL FAILURE *)
let close_by_conditional_failure constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map (
    fun tconstraint ->
      match tconstraint with
      | Lower_bound_constraint (
          Conditional_lower_bound (
            subject_type_variable,
            pattern,
            _,
            Function_type (
              parameter_type_variable,
              Constrained_type (
                body_type_variable,
                body_constraint_set
              )
            )
          ),
          conditional_result_type_variable
        ) ->
        Some (
          constraint_set
          |> Constraint_set.enum
          |> Enum.filter_map (
            fun tconstraint ->
              match tconstraint with
              | Lower_bound_constraint (
                  Restricted_type_lower_bound (
                    Restricted_type (
                      ttype,
                      Type_restriction (
                        Positive_pattern_set (positive_patterns),
                        Negative_pattern_set (negative_patterns)
                      )
                    ) as restricted_type
                  ),
                  other_subject_type_variable
                ) ->
                if (
                  (subject_type_variable = other_subject_type_variable) &&
                  (
                    is_compatible_restricted_type
                      restricted_type
                      constraint_set
                      (
                        Type_restriction
                          (
                            Positive_pattern_set Pattern_set.empty,
                            Negative_pattern_set (
                              Pattern_set.add
                                pattern
                                Pattern_set.empty
                            )
                          )
                      )
                  )
                ) then
                  Some (
                    Enum.append
                      (Constraint_set.enum body_constraint_set)
                      (
                        List.enum [
                          Lower_bound_constraint (
                            Restricted_type_lower_bound (
                              Restricted_type (
                                ttype,
                                Type_restriction (
                                  Positive_pattern_set (
                                    positive_patterns
                                  ),
                                  Negative_pattern_set (
                                    Pattern_set.add
                                      (* On the Figure, note that `\tau' is a
                                         restricted type already. The Figure
                                         Notation says, in that case, we should
                                         union the patterns in the filter
                                         together. *)
                                      pattern
                                      negative_patterns
                                  )
                                )
                              )
                            ),
                            parameter_type_variable
                          );
                          Lower_bound_constraint (
                            Type_variable_lower_bound (
                              body_type_variable
                            ),
                            conditional_result_type_variable
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

(** UNKNOWN APPLICATION *)
let close_by_unknown_application constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map (
    fun tconstraint ->
      match tconstraint with
      | Lower_bound_constraint (
          Application_lower_bound (
            function_type_variable,
            actual_parameter_type_variable
          ),
          function_return_type_variable
        ) ->
        Some (
          constraint_set
          |> Constraint_set.enum
          |> Enum.filter_map (
            fun tconstraint ->
              match tconstraint with
              | Lower_bound_constraint (
                  Restricted_type_lower_bound (
                    Restricted_type (
                      Unknown_type,
                      Type_restriction (
                        Positive_pattern_set (positive_patterns),
                        Negative_pattern_set (negative_patterns)
                      )
                    )
                  ),
                  other_function_type_variable
                ) ->
                if (function_type_variable = other_function_type_variable) then
                  Some (
                    constraint_set
                    |> Constraint_set.enum
                    |> Enum.filter_map (
                      fun tconstraint ->
                        match tconstraint with
                        | Lower_bound_constraint (
                            Restricted_type_lower_bound (restricted_type),
                            other_actual_parameter_type_variable
                          ) ->
                          if (actual_parameter_type_variable = other_actual_parameter_type_variable) then
                            Some (
                              Lower_bound_constraint (
                                Restricted_type_lower_bound (
                                  Restricted_type (
                                    Unknown_type,
                                    Type_restriction (
                                      Positive_pattern_set (
                                        Pattern_set.filter_map (
                                          fun pattern ->
                                            match pattern with
                                            | Function_pattern (parameter_pattern, body_pattern) ->
                                              if (
                                                is_compatible_restricted_type
                                                  restricted_type
                                                  constraint_set
                                                  (
                                                    Type_restriction (
                                                      Positive_pattern_set (
                                                        Pattern_set.add
                                                          parameter_pattern
                                                          Pattern_set.empty
                                                      ),
                                                      Negative_pattern_set (
                                                        Pattern_set.empty
                                                      )
                                                    )
                                                  )
                                              ) then
                                                Some (body_pattern)
                                              else
                                                None
                                            | _ -> None
                                        ) positive_patterns),
                                      Negative_pattern_set Pattern_set.empty
                                    )
                                  )
                                ) ,
                                function_return_type_variable
                              )
                            )
                          else
                            None
                        | _ -> None
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

(** UNKNOWN PROJECTION *)
let close_by_unknown_projection constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Projection_lower_bound (
              record_type_variable,
              label
            ),
            projected_type_variable
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
                          Unknown_type,
                          Type_restriction (
                            Positive_pattern_set (positive_patterns),
                            _
                          )
                        )
                      ),
                      other_record_type_variable
                    ) ->
                    if record_type_variable = other_record_type_variable then
                      let projected_patterns = project_pattern_set label positive_patterns in
                      if not (Pattern_set.is_empty projected_patterns) then
                        Some (
                          Lower_bound_constraint (
                            Restricted_type_lower_bound (
                              Restricted_type (
                                Unknown_type,
                                Type_restriction (
                                  Positive_pattern_set (projected_patterns),
                                  Negative_pattern_set (Pattern_set.empty)
                                )
                              )
                            ),
                            projected_type_variable
                          )
                        )
                      else
                        None
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

(** Entry point for non-function closure. Perform closure rules until fixpoint
    (omega) is reached. This returns the augmented constraint set with the new
    constraints as well as the original constraints. *)
let rec perform_non_function_closure perform_closure constraint_set =
  (* The order in which operations happen here is irrelevant for the correct
       behavior of the program. *)
  let closure_functions =
    [
      close_by_transitivity;
      close_by_projection;
      close_by_application;
      close_by_conditional_success;
      close_by_conditional_failure;
      close_by_unknown_application;
      close_by_unknown_projection
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
    perform_non_function_closure perform_closure augmented_constraint_set
  else
    augmented_constraint_set
;;

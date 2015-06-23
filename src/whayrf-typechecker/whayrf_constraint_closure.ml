open Batteries;;

open Whayrf_ast;;
open Whayrf_types;;

let rec is_compatible_restricted_type restricted_type constraint_set type_restriction =
  (* TODO: Not implemented yet. *)
  false

and is_compatible_type_variable type_variable constraint_set type_restriction =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Restricted_type_lower_bound (restricted_type),
            this_type_variable
          ) ->
          if type_variable = this_type_variable then
            Some (restricted_type)
          else
            None
        | _ -> None
    )
  |> Enum.exists
    (
      fun restricted_type ->
        is_compatible_restricted_type restricted_type constraint_set type_restriction
    )

and is_compatible_ttype
    ttype
    constraint_set
    (
      Type_restriction (
        Positive_pattern_set (positive_patterns),
        Negative_pattern_set (negative_patterns)
      )
    ) =
  if (positive_patterns = Pattern_set.empty) &&
     (negative_patterns = Pattern_set.empty) then
    true
  else
    (* TODO: Not implemented yet. *)
    false
;;

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
          Some (restricted_type, intermediate_type_variable)
        | _ -> None
    )
  |> Enum.map
    (
      fun (restricted_type, intermediate_type_variable) ->
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
                      Type_variable_lower_bound(intermediate_type_variable),
                      final_type_variable
                    )
                  )
                else
                  None
              | _ -> None
          )
    )
  |> Enum.concat
  |> Constraint_set.of_enum
;;

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
                            _
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
                        Positive_pattern_set (positive_pattern_set),
                        Negative_pattern_set (negative_pattern_set)
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
                                    Pattern_set.add
                                      pattern
                                      positive_pattern_set
                                  ),
                                  Negative_pattern_set (
                                    negative_pattern_set
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
                        Positive_pattern_set (positive_pattern_set),
                        Negative_pattern_set (negative_pattern_set)
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
                                    positive_pattern_set
                                  ),
                                  Negative_pattern_set (
                                    Pattern_set.add
                                      pattern
                                      negative_pattern_set
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

let close_by_function_closure constraint_set =
  (* TODO: Not implemented yet. *)
  Constraint_set.empty
;;

let rec perform_closure constraint_set =
  let closure_functions =
    [
      close_by_transitivity;
      close_by_projection;
      close_by_application;
      close_by_conditional_success;
      close_by_conditional_failure;
      close_by_unknown_application;
      close_by_unknown_projection;
      close_by_function_closure
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
    perform_closure augmented_constraint_set
  else
    augmented_constraint_set
;;

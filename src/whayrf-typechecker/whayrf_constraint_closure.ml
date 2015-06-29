open Batteries;;

open Whayrf_ast;;
open Whayrf_initial_alignment;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

let logger = Whayrf_logger.make_logger "Whayrf_constraint_closure";;

let project_pattern_set label pattern_set =
  pattern_set
  |> Pattern_set.enum
  |> Enum.filter_map (
    fun pattern ->
      match pattern with
      | Record_pattern (pattern_elements) ->
        if Ident_map.mem label pattern_elements then
          Some (Ident_map.find label pattern_elements)
        else
          None
      | _ -> raise @@ Invariant_failure "Tried to project label out of a non-record pattern."
  )
  |> Pattern_set.of_enum
;;

let rec is_subsumption_pattern_set
    (Positive_pattern_set (positive_patterns))
    (Negative_pattern_set (negative_patterns))
  =
  positive_patterns
  |> Pattern_set.enum
  |> Enum.exists
    (
      fun positive_pattern ->
        negative_patterns
        |> Pattern_set.enum
        |> Enum.exists
          (
            fun negative_pattern ->
              is_subsumption_pattern positive_pattern negative_pattern
          )
    )

and is_subsumption_pattern pattern_1 pattern_2 =
  match (pattern_1, pattern_2) with
  | (
    Record_pattern (record_patterns_1),
    Record_pattern (record_patterns_2)
  ) ->
    record_patterns_2
    |> Ident_map.enum
    |> Enum.for_all
      (
        fun (label_2, pattern_2) ->
          record_patterns_1
          |> Ident_map.enum
          |> Enum.exists
            (
              fun (label_1, pattern_1) ->
                (label_1 = label_2) &&
                (is_subsumption_pattern pattern_1 pattern_2)
            )
      )
  | (
    Function_pattern (function_pattern_1, parameter_pattern_1),
    Function_pattern (function_pattern_2, parameter_pattern_2)
  ) ->
    (is_subsumption_pattern parameter_pattern_1 parameter_pattern_2) &&
    (is_subsumption_pattern function_pattern_2 function_pattern_1)
  | (
    Pattern_variable_pattern _,
    Pattern_variable_pattern _
  ) ->
    pattern_1 = pattern_2
  | (
    Forall_pattern (ident, sub_pattern_1),
    _
  ) ->
    (* TODO: Not implemented yet. *)
    false
  | (
    _,
    Forall_pattern (ident, sub_pattern_2)
  ) ->
    (* TODO: Not implemented yet. *)
    false
  | _ -> false
;;

let rec is_compatible_restricted_type
    (
      Restricted_type (
        ttype,
        Type_restriction (
          Positive_pattern_set (restricted_type_positive_patterns),
          Negative_pattern_set (restricted_type_negative_patterns)
        )
      )
    )
    constraint_set
    (
      Type_restriction (
        Positive_pattern_set (positive_patterns),
        Negative_pattern_set (negative_patterns)
      )
    ) =
  is_compatible_ttype
    ttype
    constraint_set
    (
      Type_restriction (
        Positive_pattern_set (
          Pattern_set.union
            restricted_type_positive_patterns
            positive_patterns
        ),
        Negative_pattern_set (
          Pattern_set.union
            restricted_type_negative_patterns
            negative_patterns
        )
      )
    )

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
    let positive_patterns =
      positive_patterns
      |> Pattern_set.enum
      |> Enum.filter (
        fun pattern ->
          match pattern with
          | Pattern_variable_pattern (_) ->
            Pattern_set.mem pattern negative_patterns
          | _ -> true
      )
      |> Pattern_set.of_enum
    in
    let negative_patterns =
      negative_patterns
      |> Pattern_set.enum
      |> Enum.filter (
        fun pattern ->
          match pattern with
          | Pattern_variable_pattern (_) ->
            Pattern_set.mem pattern positive_patterns
          | _ -> true
      )
      |> Pattern_set.of_enum
    in
    match ttype with
    | Record_type (record_elements) ->
      let negative_patterns =
        negative_patterns
        |> Pattern_set.enum
        |> Enum.filter
          (
            fun pattern ->
              match pattern with
              | Record_pattern (pattern_elements) ->
                Ident_set.subset
                  (Ident_set.of_enum (Ident_map.keys pattern_elements))
                  (Ident_set.of_enum (Ident_map.keys record_elements))
              | _ -> false
          )
        |> Pattern_set.of_enum
      in
      let negative_pattern_cases =
        negative_patterns
        |> Pattern_set.enum
        |> Enum.fold
          (
            fun partial_negative_pattern_cases pattern ->
              match pattern with
              | Record_pattern (pattern_elements) ->
                partial_negative_pattern_cases
                |> Enum.map
                  (
                    fun partial_negative_pattern_case ->
                      pattern_elements
                      |> Ident_map.enum
                      |> Enum.map
                        (
                          fun (label, inner_pattern) ->
                            partial_negative_pattern_case
                            |> Pattern_set.add (
                              Record_pattern (Ident_map.add label inner_pattern Ident_map.empty)
                            )
                        )
                  )
                |> Enum.concat
              | _ -> raise @@ Invariant_failure "It's invalid to consider pattern that are not records here."
          )
          (Enum.singleton Pattern_set.empty)
      in
      let are_positive_patterns_valid =
        positive_patterns
        |> Pattern_set.enum
        |> Enum.for_all
          (
            fun pattern ->
              match pattern with
              | Record_pattern (pattern_elements) ->
                (
                  Ident_set.subset
                    (Ident_set.of_enum (Ident_map.keys pattern_elements))
                    (Ident_set.of_enum (Ident_map.keys record_elements))
                )
              | _ -> false
          )
      in
      are_positive_patterns_valid &&
      negative_pattern_cases
      |> Enum.exists
        (
          fun negative_pattern_case ->
            record_elements
            |> Ident_map.enum
            |> Enum.for_all
              (
                fun (label, type_variable) ->
                  is_compatible_type_variable
                    type_variable
                    constraint_set
                    (
                      Type_restriction (
                        Positive_pattern_set (
                          project_pattern_set label positive_patterns
                        ),
                        Negative_pattern_set (
                          project_pattern_set label negative_pattern_case
                        )
                      )
                    )
              )
        )

    | Unknown_type ->
      not (
        is_subsumption_pattern_set
          (Positive_pattern_set(positive_patterns))
          (Negative_pattern_set(negative_patterns))
      )

    | Function_type_type (
        function_type
      ) ->
      (
        positive_patterns
        |> Pattern_set.enum
        |> Enum.for_all
          (
            fun pattern ->
              constraint_set
              |> Constraint_set.enum
              |> Enum.exists
                (
                  fun tconstraint ->
                    match tconstraint with
                    | Function_pattern_matching_constraint (
                        Function_pattern_matching_constraint_positive (
                          other_function_type,
                          other_pattern
                        )
                      ) ->
                      (function_type = other_function_type) &&
                      (pattern = other_pattern)
                    | _ -> false
                )
          )
      ) &&
      (
        negative_patterns
        |> Pattern_set.enum
        |> Enum.for_all
          (
            fun pattern ->
              constraint_set
              |> Constraint_set.enum
              |> Enum.exists
                (
                  fun tconstraint ->
                    match tconstraint with
                    | Function_pattern_matching_constraint (
                        Function_pattern_matching_constraint_negative (
                          other_function_type,
                          other_pattern
                        )
                      ) ->
                      (function_type = other_function_type) &&
                      (pattern = other_pattern)
                    | _ -> false
                )
          )
      )
;;

let is_inconsistent constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.exists
    (
      fun tconstraint_1 ->
        constraint_set
        |> Constraint_set.enum
        |> Enum.exists
          (
            fun tconstraint_2 ->
              constraint_set
              |> Constraint_set.enum
              |> Enum.exists
                (
                  fun tconstraint_3 ->
                    match (tconstraint_1, tconstraint_2, tconstraint_3) with
                    | (
                      Lower_bound_constraint (
                        Application_lower_bound (function_type_variable, parameter_type_variable),
                        _
                      ),
                      Lower_bound_constraint (
                        Restricted_type_lower_bound (
                          Restricted_type (
                            function_ttype,
                            Type_restriction (
                              Positive_pattern_set (positive_patterns),
                              _
                            )
                          )
                        ),
                        other_function_type_variable
                      ),
                      Lower_bound_constraint (
                        Restricted_type_lower_bound (
                          parameter_restricted_type
                        ),
                        other_parameter_type_variable
                      )
                    ) ->
                      (function_type_variable = other_function_type_variable) &&
                      (parameter_type_variable = other_parameter_type_variable) &&
                      (
                        match function_ttype with
                        | Function_type_type _ ->
                          false
                        | Unknown_type ->
                          not (
                            positive_patterns
                            |> Pattern_set.enum
                            |> Enum.exists
                              (
                                fun (pattern) ->
                                  match pattern with
                                  | Function_pattern (parameter_pattern, _) ->
                                    is_compatible_restricted_type
                                      parameter_restricted_type
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
                                  | _ -> false
                              )
                          )
                        | _ -> true
                      )

                    | (
                      Lower_bound_constraint (
                        Projection_lower_bound (record_type_variable, label),
                        _
                      ),
                      Lower_bound_constraint (
                        Restricted_type_lower_bound (
                          Restricted_type (
                            ttype,
                            Type_restriction (
                              Positive_pattern_set (positive_patterns),
                              _
                            )
                          )
                        ),
                        other_record_type_variable
                      ),
                      _
                    ) ->
                      (record_type_variable = other_record_type_variable) &&
                      (not
                         (
                           match ttype with
                           | Record_type (record_elements) ->
                             Ident_map.mem label record_elements
                           | Unknown_type ->
                             positive_patterns
                             |> Pattern_set.enum
                             |> Enum.exists
                               (
                                 fun pattern ->
                                   match pattern with
                                   | Record_pattern (pattern_elements) ->
                                     Ident_map.mem label pattern_elements
                                   | _ -> false
                               )
                           | _ -> false
                         )
                      )

                    | (
                      Type_variable_constraint (type_variable, pattern),
                      _,
                      _
                    ) ->
                      is_compatible_type_variable
                        type_variable
                        constraint_set
                        (Type_restriction (
                            Positive_pattern_set (Pattern_set.empty),
                            Negative_pattern_set (Pattern_set.add pattern Pattern_set.empty)
                          )
                        )

                    | _ -> false
                )
          )
    )
;;

let is_consistent constraint_set =
  not (is_inconsistent constraint_set)
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
                      Restricted_type_lower_bound(restricted_type),
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

let is_transitively_closed constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.for_all
    (
      fun lower_bound_constraint ->
        match lower_bound_constraint with
        | Lower_bound_constraint (
            Restricted_type_lower_bound (restricted_type), type_variable
          ) ->
          constraint_set
          |> Constraint_set.enum
          |> Enum.for_all
            (
              fun type_variable_constraint ->
                match type_variable_constraint with
                | Lower_bound_constraint (
                    Type_variable_lower_bound (
                      other_type_variable
                    ),
                    upper_bounding_type_variable
                  ) ->
                  if type_variable = other_type_variable then(
                    (
                      match restricted_type with
                      | Restricted_type (Unknown_type, _) ->
                        logger `trace @@ "Type variable in question at least: " ^ pretty_type_variable type_variable
                      | _ -> ()
                    );
                  constraint_set
                    |> Constraint_set.enum
                    |> Enum.exists
                      (
                        fun target_constraint ->
                          match target_constraint with
                          | Lower_bound_constraint (
                              Restricted_type_lower_bound (
                                other_restricted_type
                              ),
                              other_upper_bounding_type_variable
                            ) ->
                            (restricted_type = other_restricted_type) &&
                            (upper_bounding_type_variable = other_upper_bounding_type_variable)
                          | _ -> true
                      ))
                  else
                    true
                | _ -> true
            )
        | _ -> true
    )
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

let rec perform_non_function_closure constraint_set =
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
    perform_non_function_closure augmented_constraint_set
  else
    (if is_transitively_closed augmented_constraint_set then
       augmented_constraint_set
     else
       raise @@ Invariant_failure "N step results in unclosed constraint set."
    )
;;

let rec function_pattern_search_restricted_type
    (Restricted_type (ttype, _))
    constraint_set
    pattern =
  function_pattern_search_ttype ttype constraint_set pattern

and function_pattern_search_ttype ttype constraint_set pattern =
  match (ttype, pattern) with
  | (
    Record_type (record_elements),
    Record_pattern (pattern_elements)
  ) ->
    record_elements
    |> Ident_map.enum
    |> Enum.map
      (
        fun (record_label, type_variable) ->
          pattern_elements
          |> Ident_map.enum
          |> Enum.filter_map
            (
              fun (pattern_label, pattern) ->
                if record_label = pattern_label then
                  Some (
                    function_pattern_search_type_variable
                      type_variable
                      constraint_set
                      pattern
                  )
                else
                  None
            )
          |> Enum.fold Constraint_set.union Constraint_set.empty
      )
    |> Enum.fold Constraint_set.union Constraint_set.empty

  | (
    Function_type_type (
      Function_type (
        parameter_type_variable,
        Constrained_type (
          return_type_variable,
          body_constraint_set
        )
      ) as function_type
    ),
    Function_pattern (
      parameter_pattern,
      return_pattern
    )
  ) ->
    let additional_constraints_to_test = Constraint_set.of_enum @@ List.enum [
        Lower_bound_constraint (
          Restricted_type_lower_bound (
            Restricted_type (
              Unknown_type,
              Type_restriction (
                Positive_pattern_set (
                  Pattern_set.add
                    parameter_pattern
                    Pattern_set.empty
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
      Constraint_set.union (
        Constraint_set.union additional_constraints_to_test constraint_set
      ) body_constraint_set
    in
    let closed_constraint_set_to_test =
      perform_non_function_closure constraint_set_to_test
    in
    let is_consistent_constraint_set_to_test =
      is_consistent closed_constraint_set_to_test
    in
    let new_constraint =
      (
        if is_transitively_closed closed_constraint_set_to_test then
          ()
        else
          raise @@ Invariant_failure "Testing unclosed constraint set during function pattern search."
      );
      logger `trace @@ "Constraint set checked for inconsistency in function_pattern_search: " ^ pretty_constraint_set closed_constraint_set_to_test;
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
    logger `trace @@ "New constraint to be added to the constraint set: " ^ pretty_tconstraint new_constraint;
    Constraint_set.add new_constraint Constraint_set.empty
  | _ ->
    Constraint_set.empty

and function_pattern_search_type_variable type_variable constraint_set pattern =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Restricted_type_lower_bound (restricted_type),
            other_type_variable
          ) ->
          if type_variable = other_type_variable then
            Some (function_pattern_search_restricted_type restricted_type constraint_set pattern)
          else
            None
        | _ -> None
    )
  |> Enum.fold Constraint_set.union Constraint_set.empty
;;

let perform_function_closure constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Conditional_lower_bound (
              subject_type_variable,
              pattern,
              _,
              _
            ),
            _
          ) ->
          Some (function_pattern_search_type_variable subject_type_variable constraint_set pattern)
        | _ -> None
    )
  |> Enum.fold Constraint_set.union Constraint_set.empty
;;

let rec perform_closure constraint_set =
  let closure_functions =
    [
      perform_non_function_closure;
      perform_function_closure
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

let rec unfreshen_function_value (Function_value (parameter, body)) =
  Function_value (
    unfreshen_var parameter,
    unfreshen_expr body
  )

and unfreshen_var (Var (name, _)) =
  Var (name, None)

and unfreshen_expr (Expr(clauses)) =
  Expr (
    List.map unfreshen_clause clauses
  )

and unfreshen_clause (Clause (var, clause_body)) =
  Clause (
    unfreshen_var var,
    unfreshen_clause_body clause_body
  )

and unfreshen_clause_body clause_body =
  match clause_body with
  | Value_body (value) -> Value_body (unfreshen_value value)
  | Var_body (var) -> Var_body (unfreshen_var var)
  | Appl_body (function_var, parameter_var) ->
    Appl_body (unfreshen_var function_var, unfreshen_var parameter_var)
  | Projection_body (record_var, label) ->
    Projection_body (unfreshen_var record_var, label)
  | Conditional_body (subject_var, pattern, function_then_value, function_else_value) ->
    Conditional_body (
      unfreshen_var subject_var,
      pattern,
      unfreshen_function_value function_then_value,
      unfreshen_function_value function_else_value
    )

and unfreshen_value value =
  match value with
  | Value_record (record_value) -> Value_record (unfreshen_record_value record_value)
  | Value_function (function_value) -> Value_function (unfreshen_function_value function_value)

and unfreshen_record_value (Record_value (record_elements)) =
  Record_value (
    Ident_map.map unfreshen_var record_elements
  )
;;

let build_dispatch_table constraint_set =
  fun value pattern ->
    match value with
    | Value_function (function_value) ->
      let unfreshened_function_value =
        unfreshen_function_value function_value
      in
      let function_type =
        initial_align_function unfreshened_function_value
      in
      let is_antimatch =
        constraint_set
        |> Constraint_set.enum
        |> Enum.exists
          (
            fun tconstraint ->
              match tconstraint with
              | Function_pattern_matching_constraint (
                  Function_pattern_matching_constraint_negative (
                    other_function_type,
                    other_pattern
                  )
                ) ->
                (function_type = other_function_type) &&
                (pattern = other_pattern)
              | _ -> false
          )
      in
      if is_antimatch then
        false
      else
        let is_match =
          constraint_set
          |> Constraint_set.enum
          |> Enum.exists
            (
              fun tconstraint ->
                match tconstraint with
                | Function_pattern_matching_constraint (
                    Function_pattern_matching_constraint_positive (
                      other_function_type,
                      other_pattern
                    )
                  ) ->
                  (function_type = other_function_type) &&
                  (pattern = other_pattern)
                | _ -> false
            )
        in
        if is_match then
          true
        else
          raise (Invariant_failure "Constraint absent from negative pattern set should be present in positive pattern set.")
    | _ ->
      raise (Invariant_failure "Record shouldn't not passed to dispatch table function.")
;;

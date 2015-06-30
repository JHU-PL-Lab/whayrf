open Batteries;;

open Whayrf_ast;;
open Whayrf_consistency;;
open Whayrf_constraint_closure_non_function;;
open Whayrf_initial_alignment;;
open Whayrf_notation;;
open Whayrf_pattern_subsumption;;
open Whayrf_type_compatibility;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

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
      raise (Invariant_failure "Record shouldn't be passed to dispatch table function.")
;;

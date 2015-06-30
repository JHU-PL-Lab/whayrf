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

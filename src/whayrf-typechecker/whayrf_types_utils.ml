open Batteries;;

open Whayrf_ast;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

(** Retrieve dependencies of a `function_pattern_matching_case' in a
    `dependency_graph'. *)
let dependencies function_pattern_matching_case (
    (Dependency_graph dependency_graph_elements)
    as dependency_graph
  ) =
  if Function_pattern_matching_case_map.mem function_pattern_matching_case dependency_graph_elements then
    Function_pattern_matching_case_map.find function_pattern_matching_case dependency_graph_elements
  else
    raise @@ Invariant_failure (
      "`function_pattern_matching_case' = `" ^
      pretty_function_pattern_matching_case function_pattern_matching_case ^
      "' not found in `dependency_graph' = `" ^
      pretty_dependency_graph dependency_graph ^ "'."
    )
;;

(** Find all type variables in `constraint_set'. *)
let rec type_variables_in constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            lower_bound,
            type_variable
          ) ->
          Type_variable_set.add
            type_variable
            (
              match lower_bound with
              | Restricted_type_lower_bound (
                  Restricted_type (
                    ttype,
                    _
                  )
                ) ->
                begin
                  match ttype with
                  | Record_type (
                      record_elements
                    ) ->
                    record_elements
                    |> Ident_map.values
                    |> Type_variable_set.of_enum

                  | Function_type_type (
                      function_type
                    ) ->
                    type_variables_in_function_type function_type

                  | Unknown_type ->
                    Type_variable_set.empty
                end

              | Type_variable_lower_bound (
                  type_variable
                ) ->
                Type_variable_set.singleton type_variable

              | Application_lower_bound (
                  type_variable_function,
                  type_variable_parameter
                ) ->
                Type_variable_set.of_list [
                  type_variable_function;
                  type_variable_parameter
                ]

              | Projection_lower_bound (
                  type_variable,
                  _
                ) ->
                Type_variable_set.singleton type_variable

              | Conditional_lower_bound (
                  type_variable,
                  _,
                  function_type_match,
                  function_type_antimatch
                ) ->
                Type_variable_set.add
                  type_variable (
                  Type_variable_set.union
                    (type_variables_in_function_type function_type_match)
                    (type_variables_in_function_type function_type_antimatch)
                )
            )

        | Type_variable_constraint (
            type_variable,
            _
          ) ->
            Type_variable_set.singleton (
              type_variable
            )

        | Function_pattern_matching_constraint (
            function_pattern_matching_constraint
          ) ->
          begin
            match function_pattern_matching_constraint with
            | Function_pattern_matching_constraint_positive (
                function_type,
                _
              )
            | Function_pattern_matching_constraint_negative (
                function_type,
                _
              )
            | Function_pattern_matching_constraint_squelch (
                function_type,
                _
              ) ->
              type_variables_in_function_type function_type
          end

    )
  |> Enum.fold Type_variable_set.union Type_variable_set.empty

and type_variables_in_function_type (
    Function_type (
      function_type_variable,
      Constrained_type (
        body_type_variable,
        body_constraint_set
      )
    )
  ) =
  Type_variable_set.of_list [
    function_type_variable;
    body_type_variable
  ]
  |> Type_variable_set.union @@ type_variables_in body_constraint_set
;;

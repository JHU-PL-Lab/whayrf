open Batteries;;
open Printf;;

open Whayrf_ast;;
open Whayrf_ast_pretty;;
open Whayrf_string_utils;;
open Whayrf_types;;

let pretty_type_variable (Type_variable(i)) =
  pretty_ident i
;;

let pretty_pattern_set pattern_set =
  match pattern_set with
  | Positive_pattern_set_pattern_set(Positive_pattern_set(patterns))
  | Negative_pattern_set_pattern_set(Negative_pattern_set(patterns)) ->
  concat_sep_delim "{" "}" ", "
    (patterns |> Pattern_set.enum |> Enum.map pretty_pattern)
;;

let rec pretty_constraint_set constraint_set =
  concat_sep_delim "{" "}" ", "
    (constraint_set |> Constraint_set.enum |> Enum.map pretty_tconstraint)

and pretty_constrained_type (Constrained_type (Type_variable (ident), constraint_set)) =
  pretty_ident ident ^ " \\ " ^ pretty_constraint_set constraint_set

and pretty_lower_bound lower_bound =
  match lower_bound with
  | Restricted_type_lower_bound(restricted_type) ->
    pretty_restricted_type restricted_type
  | Type_variable_lower_bound(type_variable) ->
    pretty_type_variable type_variable
  | Application_lower_bound(type_variable_function, type_variable_parameter) ->
    pretty_type_variable type_variable_function ^ " " ^ pretty_type_variable type_variable_parameter
  | Projection_lower_bound(type_variable, ident) ->
    pretty_type_variable type_variable ^ "." ^ pretty_ident ident
  | Conditional_lower_bound(type_variable, pattern, function_type_match, function_type_doesnt_match) ->
    pretty_type_variable type_variable ^ " ~ " ^ pretty_pattern pattern ^ " ? " ^
    pretty_function_type function_type_match ^ " : " ^ pretty_function_type function_type_doesnt_match

and pretty_tconstraint tconstraint =
  match tconstraint with
  | Lower_bound_constraint(lower_bound, type_variable) ->
    pretty_lower_bound lower_bound ^ " <: " ^ pretty_type_variable type_variable
  | Type_variable_constraint(type_variable, pattern) ->
    pretty_type_variable type_variable ^ " <: " ^ pretty_pattern pattern
  | Function_pattern_matching_constraint(function_pattern_matching_constraint) ->
    pretty_function_pattern_matching_constraint function_pattern_matching_constraint

and pretty_function_pattern_matching_constraint function_pattern_matching_constraint =
  match function_pattern_matching_constraint with
  | Function_pattern_matching_constraint_positive(function_type, pattern) ->
    pretty_function_type function_type ^ " +~ " ^ pretty_pattern pattern
  | Function_pattern_matching_constraint_negative(function_type, pattern) ->
    pretty_function_type function_type ^ " -~ " ^ pretty_pattern pattern
  | Function_pattern_matching_constraint_squelch(function_type, pattern) ->
    pretty_function_type function_type ^ " x~ " ^ pretty_pattern pattern

and pretty_function_type (Function_type (type_variable, constrained_type)) =
  pretty_type_variable type_variable ^ " -> " ^ pretty_constrained_type constrained_type

and pretty_ttype ttype =
  match ttype with
  | Record_type(records) ->
      concat_sep_delim "{" "}" ", "
        (records |> Ident_map.enum |> Enum.map (
            fun (ident, type_variable) ->
              pretty_ident ident ^ ": " ^ pretty_type_variable type_variable
          )
        )

  | Function_type_type(function_type) ->
    pretty_function_type function_type
  | Unknown_type ->
    "<unknown>"

and pretty_type_restriction (
    Type_restriction(
      positive_pattern_set,
      negative_pattern_set)
  ) =
  "+" ^ pretty_pattern_set (Positive_pattern_set_pattern_set(positive_pattern_set)) ^
    " -" ^ pretty_pattern_set (Negative_pattern_set_pattern_set(negative_pattern_set))

and pretty_restricted_type (Restricted_type(ttype, type_restriction)) =
  pretty_ttype ttype ^ "|" ^ pretty_type_restriction type_restriction
;;

let pretty_function_pattern_matching_case (
    Function_pattern_matching_case (
      function_type,
      pattern
    )
  ) =
  "<" ^ pretty_function_type function_type ^ ", " ^ pretty_pattern pattern ^ ">"
;;

let pretty_dependency_graph (
    Dependency_graph dependency_graph_elements
  ) =
  let graphviz_function_pattern_matching_case function_pattern_matching_case =
    "\"" ^ pretty_function_pattern_matching_case function_pattern_matching_case ^ "\""
  in
  "Graphviz source code:\ndigraph {" ^
  (
    dependency_graph_elements
    |> Function_pattern_matching_case_map.enum
    |> Enum.map
      (
        fun (
          this_function_pattern_matching_case,
          this_function_pattern_matching_case_dependencies
        ) ->
          graphviz_function_pattern_matching_case this_function_pattern_matching_case ^
          ";" ^ (
            this_function_pattern_matching_case_dependencies
            |> Function_pattern_matching_case_set.enum
            |> Enum.map
              (
                fun this_function_pattern_matching_case_dependency ->
                  graphviz_function_pattern_matching_case this_function_pattern_matching_case ^ " -> " ^
                  graphviz_function_pattern_matching_case this_function_pattern_matching_case_dependency ^ ";"
              )
            |> Enum.fold (^) ""
          )
      )
    |> Enum.fold (^) ""
  ) ^ "}"
;;

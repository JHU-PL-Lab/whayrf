open Batteries;;

open Whayrf_ast;;
open Whayrf_ast_pretty;;
open Whayrf_consistency;;
open Whayrf_constraint_closure_function;;
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

let logger = make_logger "Whayrf_dispatch_table";;

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

(* Make sure that every function pattern match that can occur has an entry in
   the dispatch table. This is not part of the theory. *)
let sanity_check constraint_set =
  let function_pattern_matching_cases =
    function_pattern_search constraint_set
  in
  function_pattern_matching_cases
  |> Function_pattern_matching_case_set.enum
  |> Enum.iter
    (
      fun (
        (

          Function_pattern_matching_case (
            function_type,
            pattern
          )
        ) as function_pattern_matching_case
      ) ->
        if (not
              (
                (
                  Constraint_set.mem
                    (
                      Function_pattern_matching_constraint (
                        Function_pattern_matching_constraint_positive (
                          function_type,
                          pattern
                        )
                      )
                    )
                    constraint_set
                ) ||
                (
                  Constraint_set.mem
                    (
                      Function_pattern_matching_constraint (
                        Function_pattern_matching_constraint_negative (
                          function_type,
                          pattern
                        )
                      )
                    )
                    constraint_set
                )
              )
           )
        then
          raise @@ Invariant_failure (
            "At least the function_pattern_matching_case `" ^
            pretty_function_pattern_matching_case function_pattern_matching_case ^
            "' is not present in the constraint set `" ^
            pretty_constraint_set constraint_set ^
            "' (others might not be present as well, there is/are " ^
            string_of_int (Function_pattern_matching_case_set.cardinal function_pattern_matching_cases)
            ^ " of them)."
          )
    )
;;

let build_dispatch_table constraint_set =
  sanity_check constraint_set;
  fun value pattern ->
    match value with
    | Value_function (function_value) ->
      let unfreshened_function_value =
        unfreshen_function_value function_value
      in
      let function_type =
        initial_align_function unfreshened_function_value
      in
      let is_negative =
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
      if is_negative then
        false
      else
        let is_positive =
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
        if is_positive then
          true
        else
          (
            logger `fatal ("Function type: `" ^ pretty_function_type function_type ^ "'.");
            logger `fatal ("Pattern: `" ^ pretty_pattern pattern ^ "'.");
            logger `fatal ("Constraint set: `" ^ pretty_constraint_set constraint_set ^ "'.");
          raise (Invariant_failure "Both positive and negative function pattern matching constraints (function_type +~ pattern or function_type -~ pattern) absent from constraint set.")
          )
    | _ ->
      raise (Invariant_failure "Record shouldn't be passed to dispatch table function.")
;;

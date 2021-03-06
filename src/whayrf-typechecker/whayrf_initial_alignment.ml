open Batteries;;

open Whayrf_ast;;
open Whayrf_types;;

(** Alignment is the operation that, given a value, figures out an initial
    constrained type for it. This constrained type can later be enhanced by
    performing constraint closure on its constraint set.
*)

(** Perform initial alignment on expressions (lists of clauses) (first section
    of figure).
*)
let rec initial_align_expr (Expr(clauses)) =
  clauses
  |> List.map initial_align_clause
  |> List.reduce (
    fun (Constrained_type (_, constraint_set_1))
      (Constrained_type (type_variable_2, constraint_set_2)) ->
      Constrained_type (
        type_variable_2, (Constraint_set.union constraint_set_1 constraint_set_2)
      )
  )

(** Perform initial alignment on clauses (second section of figure). *)
and initial_align_clause (Clause (Var(left_ident, _), body)) =
  let type_variable = Type_variable (left_ident) in
  match body with
  (* RECORD *)
  | Value_body (Value_record(Record_value(record_elements))) ->
    Constrained_type (
      type_variable,
      Constraint_set.add
        (
          Lower_bound_constraint (
            Restricted_type_lower_bound (
              Restricted_type (
                Record_type (
                  Ident_map.map
                    (
                      fun (Var(ident, _)) ->
                        Type_variable (ident)
                    )
                    record_elements
                ),
                Type_restriction (
                  Positive_pattern_set(Pattern_set.empty),
                  Negative_pattern_set(Pattern_set.empty)
                )
              )
            ),
            type_variable
          )
        )
        Constraint_set.empty
    )

  (* PROJECTION *)
  | Projection_body (Var(record_ident, _), label) ->
    Constrained_type (
      type_variable,
      Constraint_set.add
        (
          Lower_bound_constraint (
            Projection_lower_bound (
              Type_variable (record_ident),
              label
            ),
            type_variable
          )
        )
        Constraint_set.empty
    )

  (* FUNCTION *)
  | Value_body (Value_function(function_value)) ->
    Constrained_type (
      type_variable,
      Constraint_set.add
        (
          Lower_bound_constraint (
            Restricted_type_lower_bound (
              Restricted_type (
                Function_type_type (
                  initial_align_function function_value
                ),
                Type_restriction (
                  Positive_pattern_set(Pattern_set.empty),
                  Negative_pattern_set(Pattern_set.empty)
                )
              )
            ),
            type_variable
          )
        )
        Constraint_set.empty
    )

  (* VARIABLE *)
  | Var_body (Var(right_ident, _)) ->
    Constrained_type (
      type_variable,
      Constraint_set.add
        (
          Lower_bound_constraint (
            Type_variable_lower_bound (
              Type_variable (right_ident)
            ),
            type_variable
          )
        )
        Constraint_set.empty
    )

  (* APPLICATION *)
  | Appl_body (Var(function_ident, _), Var(parameter_ident, _)) ->
    Constrained_type (
      type_variable,
      Constraint_set.add
        (
          Lower_bound_constraint (
            Application_lower_bound (
              Type_variable (function_ident),
              Type_variable (parameter_ident)
            ),
            type_variable
          )
        )
        Constraint_set.empty
    )

  (* CONDITIONAL *)
  | Conditional_body (Var (subject_ident, _), pattern, function_value_match, function_value_doesnt_match) ->
    Constrained_type (
      type_variable,
      Constraint_set.add
        (
          Lower_bound_constraint (
            Conditional_lower_bound (
              Type_variable (subject_ident),
              pattern,
              initial_align_function function_value_match,
              initial_align_function function_value_doesnt_match
            ),
            type_variable
          )
        )
        Constraint_set.empty
    )

(** Perform initial alignment on function values (third section of figure). *)
and initial_align_function (Function_value (Var(parameter_ident, _), body)) =
  Function_type (
    (Type_variable parameter_ident),
    initial_align_expr body
  )
;;

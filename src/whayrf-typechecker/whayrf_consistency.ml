open Batteries;;

open Whayrf_ast;;
open Whayrf_initial_alignment;;
open Whayrf_notation;;
open Whayrf_pattern_subsumption;;
open Whayrf_type_compatibility;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

(** Perform inconsistency checks. This function doesn't perform a single step of
    the checks, but the fixpoint. *)
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

                    (* APPLICATION FAILURE and UNKNOWN APPLICATION FAILURE *)
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
                        (* By APPLICATION FAILURE, this constraints are _not_
                           inconsistent. *)
                        | Function_type_type _ ->
                          false
                        (* UNKNOWN APPLICATION FAILURE *)
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
                        (* Any other type that shows up in the place of a
                           function in an application is an inconsistency. *)
                        | _ -> true
                      )

                    (* PROJECTION FAILURE *)
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
                        (* HAS FIELD *)
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

                    (* UPPER-BOUNDING PATTERN *)
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

                    (* AMBIGUOUS DISPATCH *)
                    | (
                      Function_pattern_matching_constraint (
                        Function_pattern_matching_constraint_positive (
                          positive_function_type, positive_pattern
                        )
                      ),
                      Function_pattern_matching_constraint (
                        Function_pattern_matching_constraint_negative (
                          negative_function_type, negative_pattern
                        )
                      ),
                      _
                    ) ->
                      (positive_function_type = negative_function_type) &&
                      (positive_pattern = negative_pattern)

                    | _ -> false
                )
          )
    )
;;

let is_consistent constraint_set =
  not (is_inconsistent constraint_set)
;;

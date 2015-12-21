open Batteries;;

open Whayrf_ast;;
open Whayrf_initial_alignment;;
open Whayrf_notation;;
open Whayrf_pattern_subsumption;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

(** Implement Type Compatibility rules. There are three kinds of rules, those
    that work on restricted types, those that works on raw types (ttype) and
    those that work on type variables. *)

(** TYPE SELECTION *)
let rec is_compatible_type_variable type_variable constraint_set type_restriction =
  constraint_set
  |> Constraint_set.enum
  |> Enum.exists
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Restricted_type_lower_bound (restricted_type),
            other_type_variable
          ) ->
          (type_variable = other_type_variable) &&
          (is_compatible_restricted_type restricted_type constraint_set type_restriction)
        | _ -> false
    )

(** FILTERED TYPE *)
and is_compatible_restricted_type
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

and is_compatible_ttype
    ttype
    constraint_set
    (
      Type_restriction (
        Positive_pattern_set (positive_patterns),
        Negative_pattern_set (negative_patterns)
      )
    ) =
  (* LEAF *)
  if (positive_patterns = Pattern_set.empty) &&
     (negative_patterns = Pattern_set.empty) then
    true
  else
    match ttype with

    (* RECORD *)
    (* That's a hard one, you're in for a treat! *)
    | Record_type (record_elements) ->
      (* ABSENT FIELD *)
      (* Start by filtering out of the negative pattern set record patterns that
         antimatch the type because it refers to labels that the type doesn't
         have.

         Note that this implementation doesn't restrict the rule to singleton
         record patterns, diverging from the spec. That's on purpose,
         though. It's still correct, and the only reason the rule was written
         that way was to make it look better on the paper.

         This is guaranteed to be correct because RECORD EXTENSION would
         simplify the record patterns on the negative pattern set until the
         ABSENT FIELD rule would wipe them out anyway. We're only making it
         do it earlier.

         While we're filtering the negative pattern set anyway, we take the
         opportunity to wipe out all patterns that are not record patterns! They
         obviously antimatch. *)
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
              | _ ->
                (* Wipe out all patterns that are not record patterns as they
                   trivially antimatch, we don't need to work on them to prove
                   anything. *)
                false
          )
        |> Pattern_set.of_enum
      in

      (* RECORD EXTENSION *)
      (* This is going to run the rule to its fixpoint, instead of just
         once. The idea here is to create all possible subsets of record
         patterns by removing all possible fields in all possible ways. This
         creates a stream of cases of negative pattern sets that are going to be
         later tested by the RECORD rule.

         Think of this like a Cartesian Product. We start with the empty set,
         and recursively add new cases by adding a new pattern at a time for
         each of the previous cases. *)
      let negative_pattern_set_cases =
        negative_patterns
        |> Pattern_set.enum
        |> Enum.fold
          (
            fun partial_negative_pattern_set_cases pattern ->
              match pattern with
              | Record_pattern (pattern_elements) ->
                partial_negative_pattern_set_cases
                |> Enum.map
                  (
                    fun partial_negative_pattern_set_case ->
                      pattern_elements
                      |> Ident_map.enum
                      |> Enum.map
                        (
                          fun (label, inner_pattern) ->
                            Pattern_set.add
                              (
                                Record_pattern (Ident_map.add label inner_pattern Ident_map.empty)
                              )
                              partial_negative_pattern_set_case
                        )
                  )
                |> Enum.concat
              | _ -> raise @@ Invariant_failure "It's invalid to consider pattern that are not records here they should have been previously weeded out by the ABSENT FIELD rule application."
          )
          (Enum.singleton Pattern_set.empty)
      in

      (* RECORD *)
      (* All the prep work has been done this far. We proceed to the bulk of the
         RECORD rule. The hard part is over! *)
      (
        (* This checks if it holds the subset relation between the fields on the
           pattern and the fields on the type. *)
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
              (* If the pattern is not a record pattern, then there's no way
                 it's going to match. We fail immediately. *)
              | _ -> false
          )
      ) &&
      (* We now traverse the cases that we generated earlier and try to find one
         that can be used to build the proof. *)
      negative_pattern_set_cases
      |> Enum.exists
        (
          fun negative_pattern_set_case ->
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
                          project_pattern_set label negative_pattern_set_case
                        )
                      )
                    )
              )
        )

    (* UNKNOWN *)
    | Unknown_type ->
      not (
        is_subsumption_pattern_set
          (Positive_pattern_set(positive_patterns))
          (Negative_pattern_set(negative_patterns))
      )

    (* FUNCTION MATCH and FUNCTION ANTI-MATCH *)
    (* These two are implemented together because they are almost identical,
       only concerned with positive and negative pattern sets.

       Instead of applying one step of the rule, we perform the fixpoint by
       considering every pattern in the pattern set. *)
    | Function_type_type (
        function_type
      ) ->

      (* FUNCTION MATCH *)
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

      (* FUNCTION ANTI-MATCH *)
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

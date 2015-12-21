open Batteries;;

open Whayrf_ast;;
open Whayrf_utils;;

(** Exception used to control flow of pattern constraint closure execution. This
    is necessary because we build new constraints and check for inconsistencies
    along the way. If we happen to find an inconsistent constraint, we give up
    on the task entirely and return early. *)
exception Contradiction_found;;

(** Pattern constraints are pairs of patterns that represent a "is
    subsumed by" relation. *)
type pattern_constraint =
  | Pattern_constraint of pattern * pattern
;;

module Pattern_constraint_order =
struct
  type t = pattern_constraint
  let compare = compare
end
;;

module Pattern_constraint_set = Set.Make(Pattern_constraint_order);;

(** Performs the initial alignment between a pair of patterns to a
    pattern constraint. *)
let initial_alignment pattern_1 pattern_2 =
  Pattern_constraint_set.singleton @@ Pattern_constraint (pattern_1, pattern_2)
;;

(** Traverse the pattern constraint consuming the constraints, generating new
    constraints and raising Contradiction_found in case a contradiction was
    found on the pattern constraint set.

    Callers of this function should catch the Contradiction_found exception that
    is only used for flow control.

    This is where the bulk of the Pattern Subsumption rules is implemented. *)
let digest pattern_constraint_set =
  pattern_constraint_set
  |> Pattern_constraint_set.enum
  |> Enum.map
    (
      fun (
        (
          Pattern_constraint (
            pattern_1,
            pattern_2
          )
        )
      ) ->
        match (pattern_1, pattern_2) with
        (* RECORD *)
        | (
          Record_pattern (record_patterns_1),
          Record_pattern (record_patterns_2)
        ) ->
          if Ident_set.subset
              (Ident_set.of_enum (Ident_map.keys record_patterns_2))
              (Ident_set.of_enum (Ident_map.keys record_patterns_1))
          then
            record_patterns_2
            |> Ident_map.enum
            |> Enum.map
              (
                fun (label_2, pattern_2) ->
                  record_patterns_1
                  |> Ident_map.enum
                  |> Enum.filter_map
                    (
                      fun (label_1, pattern_1) ->
                        if (label_1 = label_2) then
                          Some (
                            Pattern_constraint (
                              pattern_1, pattern_2
                            )
                          )
                        else
                          None
                    )
                  |> Pattern_constraint_set.of_enum
              )
            |> Enum.fold Pattern_constraint_set.union Pattern_constraint_set.empty
          else
            raise Contradiction_found

        (* FUNCTION *)
        | (
          Function_pattern (parameter_pattern_1, return_pattern_1),
          Function_pattern (parameter_pattern_2, return_pattern_2)
        ) ->
          Pattern_constraint_set.of_enum @@ List.enum [
            Pattern_constraint (return_pattern_1, return_pattern_2);
            Pattern_constraint (parameter_pattern_2, parameter_pattern_1)
          ]
        (* Fallback. If we can't apply any of those rules, there's something
           wrong with the constraint. *)
        | _ -> raise Contradiction_found
    )
  |> Enum.fold Pattern_constraint_set.union Pattern_constraint_set.empty
;;

(** Perform Pattern Constraint Closure (i.e. the one that is NOT on the paper).

    This function doesn't perform a single step, but the fixpoint (omega). This
    returns the pattern constraint set with the new constraints but not the old
    ones. *)
let rec perform_pattern_constraint_closure pattern_constraint_set =
  let digested_constraint_set =
    digest pattern_constraint_set
  in
  if pattern_constraint_set <> digested_constraint_set then
    perform_pattern_constraint_closure digested_constraint_set
  else
    digested_constraint_set
;;

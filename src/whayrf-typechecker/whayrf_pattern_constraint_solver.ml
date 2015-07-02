open Batteries;;

open Whayrf_ast;;
open Whayrf_utils;;

(** The FORALL ELIM Pattern Subsumption rule requires the implementation to pick
    a pattern to substitute for the pattern variable. In order to pick the right
    pattern, we need a kind of Hindley-Milner Type System with Let Polymorphism
    for the pattern variables.

    We perform a constraint closure with the purpose of unifying the pattern
    variables with patterns that enable a proof to be build. *)

(** Exception used to control flow of pattern constraint closure execution. This
    is necessary because we build new constraints and check for inconsistencies
    along the way. If we happen to find an inconsistent constraint, we give up
    on the task entirely and return early. *)
exception Contradiction_found;;

(** Supertype of pattern that includes Rigid and Wobbly variables. Rigid
    variables are those that "the adversary" has chosen for us. Wobbly variables
    we can pick to conform to expectations and make the proofs possible. *)
type augmented_pattern =
  | Record_pattern of augmented_pattern Ident_map.t
  | Function_pattern of augmented_pattern * augmented_pattern
  | Pattern_variable_pattern of pattern_variable
  | Forall_pattern of pattern_variable * augmented_pattern
  | Rigid_pattern_variable of int
  | Wobbly_pattern_variable of int
;;

(** Pattern constraints are pairs of augmented_patterns that represent a "is
    subsumed by" relation. *)
type pattern_constraint =
  | Pattern_constraint of augmented_pattern * augmented_pattern
;;

module Pattern_constraint_order =
struct
  type t = pattern_constraint
  let compare = compare
end
;;

module Pattern_constraint_set = Set.Make(Pattern_constraint_order);;

(** Counter used to provide new rigid pattern variables. *)
let rigid_pattern_variable_counter = ref 0;;

(** Returns a new rigid pattern variable guaranteed to never be seen by the
    program. *)
let new_rigid_pattern_variable () =
  let current_rigid_pattern_variable = !rigid_pattern_variable_counter in
  rigid_pattern_variable_counter := current_rigid_pattern_variable + 1;
  Rigid_pattern_variable current_rigid_pattern_variable
;;

(** Counter used to provide new wobbly pattern variables. *)
let wobbly_pattern_variable_counter = ref 0;;

(** Returns a new wobbly pattern variable guaranteed to never be seen by the
    program. *)
let new_wobbly_pattern_variable () =
  let current_wobbly_pattern_variable = !wobbly_pattern_variable_counter in
  wobbly_pattern_variable_counter := current_wobbly_pattern_variable + 1;
  Wobbly_pattern_variable current_wobbly_pattern_variable
;;

(** Perform substitution on augmented_patterns. It's the operation represented by
    $\pi\[\pi' \ \beta\]$. A.k.a. alpha substitution. *)
let rec substitute_augmented_pattern_variable
    augmented_pattern
    new_augmented_pattern
    old_augmented_pattern_variable =
  match augmented_pattern with
  | Record_pattern (augmented_pattern_elements) ->
    Record_pattern (
      Ident_map.map
        (
          fun subaugmented_pattern ->
            substitute_augmented_pattern_variable subaugmented_pattern new_augmented_pattern old_augmented_pattern_variable
        )
        augmented_pattern_elements
    )
  | Function_pattern (function_augmented_pattern, parameter_augmented_pattern) ->
    Function_pattern (
      substitute_augmented_pattern_variable function_augmented_pattern new_augmented_pattern old_augmented_pattern_variable,
      substitute_augmented_pattern_variable parameter_augmented_pattern new_augmented_pattern old_augmented_pattern_variable
    )
  | Pattern_variable_pattern (this_augmented_pattern_variable) ->
    if this_augmented_pattern_variable = old_augmented_pattern_variable then
      new_augmented_pattern
    else
      augmented_pattern
  | Forall_pattern (this_augmented_pattern_variable, subaugmented_pattern) ->
    (* Prevents shadowed variables from being renamed. *)
    if this_augmented_pattern_variable = old_augmented_pattern_variable then
      augmented_pattern
    else
      Forall_pattern (
        old_augmented_pattern_variable,
        substitute_augmented_pattern_variable
          subaugmented_pattern
          new_augmented_pattern
          old_augmented_pattern_variable
      )
  | Rigid_pattern_variable _ | Wobbly_pattern_variable _ ->
    augmented_pattern
;;

(** Promotes a regular pattern to an augmented_pattern. *)
let rec augment_pattern pattern =
  match pattern with
  | Whayrf_ast.Record_pattern (pattern_elements) ->
    Record_pattern (
      Ident_map.map augment_pattern pattern_elements
    )
  | Whayrf_ast.Function_pattern (function_pattern, parameter_pattern) ->
    Function_pattern (
      augment_pattern function_pattern,
      augment_pattern parameter_pattern
    )
  | Whayrf_ast.Pattern_variable_pattern (pattern_variable) ->
    Pattern_variable_pattern (pattern_variable)
  | Whayrf_ast.Forall_pattern (pattern_variable, subpattern) ->
    Forall_pattern (pattern_variable, augment_pattern subpattern)
;;

(** Performs the initial alignment between a pair of patterns to an augmented
    pattern constraint. *)
let initial_alignment pattern_1 pattern_2 =
  Pattern_constraint_set.singleton @@
  Pattern_constraint (
    augment_pattern pattern_1,
    augment_pattern pattern_2
  )
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
            augmented_pattern_1,
            augmented_pattern_2
          )
        ) as pattern_constraint
      ) ->
        match (augmented_pattern_1, augmented_pattern_2) with
        (* RECORD *)
        | (
          Record_pattern (record_augmented_patterns_1),
          Record_pattern (record_augmented_patterns_2)
        ) ->
          if Ident_set.subset
              (Ident_set.of_enum (Ident_map.keys record_augmented_patterns_2))
              (Ident_set.of_enum (Ident_map.keys record_augmented_patterns_1))
          then
            record_augmented_patterns_2
            |> Ident_map.enum
            |> Enum.map
              (
                fun (label_2, augmented_pattern_2) ->
                  record_augmented_patterns_1
                  |> Ident_map.enum
                  |> Enum.filter_map
                    (
                      fun (label_1, augmented_pattern_1) ->
                        if (label_1 = label_2) then
                          Some (
                            Pattern_constraint (
                              augmented_pattern_1, augmented_pattern_2
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
          Function_pattern (parameter_augmented_pattern_1, return_augmented_pattern_1),
          Function_pattern (parameter_augmented_pattern_2, return_augmented_pattern_2)
        ) ->
          Pattern_constraint_set.of_enum @@ List.enum [
            Pattern_constraint (return_augmented_pattern_1, return_augmented_pattern_2);
            Pattern_constraint (parameter_augmented_pattern_2, parameter_augmented_pattern_1)
          ]

        (* VARIABLE *)
        | (
          Rigid_pattern_variable _,
          Rigid_pattern_variable _
        ) ->
          if augmented_pattern_1 = augmented_pattern_2 then
            Pattern_constraint_set.empty
          else
            raise Contradiction_found

        (* FORALL INTRO *)
        (* It's important for the correct behavior of the program that FORALL
           INTRO is tried before FORALL ELIM because variables need to be
           introduced before they can be analyzed. *)
        | (
          _,
          Forall_pattern (old_pattern_variable, sub_pattern_2)
        ) ->
          let new_pattern_variable = new_rigid_pattern_variable () in
          let renamed_pattern =
            substitute_augmented_pattern_variable
              sub_pattern_2
              new_pattern_variable
              old_pattern_variable
          in
          Pattern_constraint_set.singleton (
            Pattern_constraint (augmented_pattern_1, renamed_pattern)
          )

        (* FORALL ELIM *)
        | (
          Forall_pattern (old_pattern_variable, sub_pattern_1),
          _
        ) ->
          let new_pattern_variable = new_wobbly_pattern_variable () in
          let renamed_pattern =
            substitute_augmented_pattern_variable
              sub_pattern_1
              new_pattern_variable
              old_pattern_variable
          in
          Pattern_constraint_set.singleton (
            Pattern_constraint (renamed_pattern, augmented_pattern_2)
          )

        (* Ignore wobbly pattern variables, they pass right through the
           digestion unchanged (gross!). *)
        | (
          Wobbly_pattern_variable _,
          _
        )
        | (
          _,
          Wobbly_pattern_variable _
        ) ->
          Pattern_constraint_set.singleton pattern_constraint

        | (
          Pattern_variable_pattern _,
          _
        )
        | (
          _,
          Pattern_variable_pattern _
        ) ->
          raise @@ Invariant_failure "All regular pattern variables should be properly quantified. Either there's a problem on the pattern, or your (i.e. my) substitution function is wrong."

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

(** Close wobbly variables by transitivity.

    Returns the pattern constraint set with the rules to be added. *)
let close_by_transitivity pattern_constraint_set =
  pattern_constraint_set
  |> Pattern_constraint_set.enum
  |> Enum.map
    (
      fun pattern_constraint_1 ->
        pattern_constraint_set
        |> Pattern_constraint_set.enum
        |> Enum.filter_map
          (
            fun pattern_constraint_2 ->
              match (pattern_constraint_1, pattern_constraint_2) with
              (* TRANSITIVITY *)
              | (
                Pattern_constraint (
                  augmented_pattern_left_1, Wobbly_pattern_variable(wobbly_count_right_1)
                ),
                Pattern_constraint (
                  Wobbly_pattern_variable(wobbly_count_left_2), augmented_pattern_right_2
                )
              ) ->
                if wobbly_count_right_1 = wobbly_count_left_2 then
                  Some (
                    Pattern_constraint (
                      augmented_pattern_left_1, augmented_pattern_right_2
                    )
                  )
                else
                  None

              (* Fallback. *)
              | _ ->
                None
          )
        |> Pattern_constraint_set.of_enum
    )
  |> Enum.fold Pattern_constraint_set.union Pattern_constraint_set.empty
;;

(** Transitive closure of wobbly variables. It introduces new pattern
    constraints and runs to the fixpoint of the operation, instead of a single
    step.

    Returns the pattern constraint set with the original rules as well as the
    ones that were added. *)
let rec perform_transitive_pattern_closure pattern_constraint_set =
  let augmented_constraint_set =
    Pattern_constraint_set.union pattern_constraint_set @@ close_by_transitivity pattern_constraint_set
  in
  if pattern_constraint_set <> augmented_constraint_set then
    perform_transitive_pattern_closure augmented_constraint_set
  else
    augmented_constraint_set
;;

(** Filter out the pattern constraints that include a wobbly variable. *)

let filter_out_wobbly_variables pattern_constraint_set =
  pattern_constraint_set
  |> Pattern_constraint_set.enum
  |> Enum.filter
    (
      fun pattern_constraint ->
        match pattern_constraint with
        | Pattern_constraint (
            Wobbly_pattern_variable (_),
            _
          )
        | Pattern_constraint (
            _,
            Wobbly_pattern_variable (_)
          )
          ->
          false
        | _ -> true
    )
  |> Pattern_constraint_set.of_enum
;;

open Batteries;;

open Whayrf_ast;;
open Whayrf_ast_pretty;;
open Whayrf_consistency;;
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

let logger = make_logger "Whayrf_constraint_closure_function";;

type function_pattern_match =
  | Function_pattern_match of function_type * pattern
;;

module Function_pattern_match_order =
struct
  type t = function_pattern_match
  let compare = compare
end;;

module Function_pattern_match_set = Set.Make(Function_pattern_match_order);;

(** FUN PATS

    Find function type-pattern pairs in the constraint set. *)
let find_function_pattern_matches constraint_set =
  constraint_set
  |> Constraint_set.enum
  |> Enum.filter_map
    (
      fun tconstraint ->
        match tconstraint with
        | Lower_bound_constraint (
            Restricted_type_lower_bound (
              Restricted_type (
                Function_type_type (
                  function_type
                ),
                _
              )
            ),
            type_variable
          ) ->
          Some (
            constraint_set
            |> Constraint_set.enum
            |> Enum.filter_map
              (
                fun tconstraint ->
                  match tconstraint with

                  (* S_f *)
                  | Type_variable_constraint (
                      other_type_variable,
                      (
                        Function_pattern (
                          _,
                          _
                        ) as pattern
                      )
                    )

                  (* S_p *)
                  | Lower_bound_constraint (
                      Conditional_lower_bound (
                        other_type_variable,
                        (
                          Function_pattern (
                            _,
                            _
                          ) as pattern
                        ),
                        _,
                        _
                      ),
                      _
                    ) ->
                    if type_variable = other_type_variable then
                      Some (
                        Function_pattern_match (
                          function_type,
                          pattern
                        )
                      )
                    else
                      None

                  | _ -> None
              )
          )
        | _ -> None
    )
  |> Enum.concat
  |> Function_pattern_match_set.of_enum
;;

(* FUN MATCH

   Whether a function_type matches a pattern in the context of a constraint
   set.

   It is a assumed that the constraint_set is already closed over non-function
   closure. So the N-closure in the rule is not performed. *)
let is_function_pattern_match
    perform_closure
    (
      Function_type (
        parameter_type_variable,
        Constrained_type (
          return_type_variable,
          body_constraint_set
        )
      )
    )
    function_pattern
    constraint_set =
  match function_pattern with
  | Function_pattern (
      parameter_pattern,
      return_pattern
    ) ->
    let squelches =
      constraint_set
      |> find_function_pattern_matches
      |> Function_pattern_match_set.enum
      |> Enum.map
        (
          fun (
            Function_pattern_match (
              function_type,
              pattern
            )
          ) ->
            Function_pattern_matching_constraint (
              Function_pattern_matching_constraint_squelch (
                function_type,
                pattern
              )
            )
        )
      |> Constraint_set.of_enum
    in
    let parameter_return_constraints =
      let parameter_constraint =
        Lower_bound_constraint (
          Restricted_type_lower_bound (
            Restricted_type (
              Unknown_type,
              Type_restriction (
                Positive_pattern_set (
                  Pattern_set.singleton parameter_pattern
                ),
                Negative_pattern_set (
                  Pattern_set.empty
                )
              )
            )
          ),
          parameter_type_variable
        )
      in
      let return_constraint =
        Type_variable_constraint (
          return_type_variable,
          return_pattern
        )
      in
      Constraint_set.of_list [parameter_constraint; return_constraint]
    in
    let subordinate_closure_constraint_set =
      List.reduce Constraint_set.union [
        parameter_return_constraints;
        body_constraint_set;
        constraint_set;
        squelches
      ]
    in
    let closed_subordinate_closure_constraint_set =
      perform_closure subordinate_closure_constraint_set
    in
    is_consistent closed_subordinate_closure_constraint_set
  | _ ->
    raise (Invariant_failure "`is_function_pattern_match' called with something other than a function pattern.")
;;

(** Perform Function Constraint Closure (i.e. the one with the F superscript).

    This function doesn't perform a single step, but the fixpoint (omega). This
    returns the augmented constraint set with the new constraints as well as the
    original constraints. *)
let perform_function_closure perform_closure constraint_set =
  let augmented_constraint_set =
    constraint_set
    |> Constraint_set.enum
    |> Enum.filter_map
      (
        fun tconstraint ->
          match tconstraint with
          (* FUNCTION CLOSURE *)
          | Lower_bound_constraint (
              Conditional_lower_bound (
                type_variable,
                pattern,
                _,
                _
              ),
              _
            )

          (* FUNCTION CLOSURE (UPPER BOUNDING PATTERN) *)
          | Type_variable_constraint (
              type_variable,
              pattern
            ) ->
            Some (function_pattern_search_type_variable perform_closure type_variable constraint_set pattern)
          | _ -> None
      )
    |> Enum.fold Constraint_set.union constraint_set
  in
  logger `trace ("New constraints generated by function constraint closure: `" ^ pretty_constraint_set (Constraint_set.diff augmented_constraint_set constraint_set) ^ "'.");
  augmented_constraint_set
;;

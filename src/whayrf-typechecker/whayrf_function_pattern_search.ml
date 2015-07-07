open Batteries;;

open Whayrf_ast;;
open Whayrf_ast_pretty;;
open Whayrf_consistency;;
open Whayrf_initial_alignment;;
open Whayrf_logger;;
open Whayrf_notation;;
open Whayrf_pattern_subsumption;;
open Whayrf_type_compatibility;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

let logger = make_logger "Whayrf_function_pattern_search";;

type function_pattern_matching_case = Function_pattern_matching_case of function_type * pattern;;

module Function_pattern_matching_case_order =
struct
  type t = function_pattern_matching_case
  let compare = compare
end
;;
module Function_pattern_matching_case_set = Set.Make(Function_pattern_matching_case_order);;

(** For correctness, on the FORALL rule, when the refreshing happens, it needs
    to be consistent. I.e., when a pattern variable was substituted, it's always
    substituted with the same fresh pattern variable. *)
module Pattern_variable_order =
struct
  type t = pattern_variable
  let compare = compare
end
;;
module Pattern_variable_map = Map.Make(Pattern_variable_order);;

type forall_consistent_freshness_type = pattern_variable Pattern_variable_map.t;;

let forall_consistent_freshness : forall_consistent_freshness_type ref = ref Pattern_variable_map.empty;;

(** Find Function Matching looks for all pairs of function types and patterns
    that can be explored by the Function Pattern Search. It comes in three
    flavors, one that takes a raw type (ttype), one that takes a restricted type
    and another that takes a type variable.

    It's inspired by Function Pattern Search. *)
let rec find_function_pattern_matching_cases_ttype ttype constraint_set pattern =
  match (ttype, pattern) with
  (* FUNCTION MATCH and FUNCTION ANTI-MATCH *)
  (* These rules are almost identical, so they share the code. *)
  | (
    Function_type_type (
      function_type
    ),
    Function_pattern (
      _
    )
  )

  (* FORALL *)
  | (
    Function_type_type (
      function_type
    ),
    Forall_pattern (
      _
    )
  ) ->
    Function_pattern_matching_case_set.singleton
      (Function_pattern_matching_case (function_type, pattern))

  (* RECORD *)
  (* Align the record type with the record pattern and recurse on the type
     variable under the record label. This implementation doesn't apply the rule
     once, but performs the fixpoint and returns the resulting set. *)
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
                    find_function_pattern_matching_cases_type_variable
                      type_variable
                      constraint_set
                      pattern
                  )
                else
                  None
            )
          |> Enum.fold Function_pattern_matching_case_set.union Function_pattern_matching_case_set.empty
      )
    |> Enum.fold Function_pattern_matching_case_set.union Function_pattern_matching_case_set.empty

  | _ ->
    Function_pattern_matching_case_set.empty

(** FILTERED TYPE *)
(* Simply ignore the filter. *)
and find_function_pattern_matching_cases_restricted_type
    (Restricted_type (ttype, _))
    constraint_set
    pattern =
  find_function_pattern_matching_cases_ttype ttype constraint_set pattern

(** TYPE SELECTION *)
(* This implementation doesn't apply the rule once, but performs the fixpoint
   and returns the resulting set. *)
and find_function_pattern_matching_cases_type_variable type_variable constraint_set pattern =
  logger `trace ("Looking for type variable `" ^ pretty_type_variable type_variable ^ "' in the constraint set: `"  ^ pretty_constraint_set constraint_set ^ "', and matching it with pattern `" ^ pretty_pattern pattern ^ "'.");
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
            Some (find_function_pattern_matching_cases_restricted_type restricted_type constraint_set pattern)
          else
            None
        | _ -> None
    )
  |> Enum.fold Function_pattern_matching_case_set.union Function_pattern_matching_case_set.empty
;;

(** Function Pattern Search generates constraints based on function
    patterns. This returns the only the new constraints and not the original
    ones. It comes in three flavors, one that takes a raw type (ttype), one
    that takes a restricted type and another that takes a type variable.

    This is used by Function Constraint Closure. *)
let rec function_pattern_search_ttype
    perform_closure
    ttype
    constraint_set
    pattern =
  let function_pattern_matching_cases =
    find_function_pattern_matching_cases_ttype
      ttype
      constraint_set
      pattern
  in
  perform_function_pattern_search
    perform_closure
    function_pattern_matching_cases
    constraint_set
    pattern

and function_pattern_search_restricted_type
    perform_closure
    restricted_type
    constraint_set
    pattern =
  let function_pattern_matching_cases =
    find_function_pattern_matching_cases_restricted_type
      restricted_type
      constraint_set
      pattern
  in
  perform_function_pattern_search
    perform_closure
    function_pattern_matching_cases
    constraint_set
    pattern

and function_pattern_search_type_variable
    perform_closure
    type_variable
    constraint_set
    pattern =
  let function_pattern_matching_cases =
    find_function_pattern_matching_cases_type_variable
      type_variable
      constraint_set
      pattern
  in
  perform_function_pattern_search
    perform_closure
    function_pattern_matching_cases
    constraint_set
    pattern

and perform_function_pattern_search
    perform_closure
    function_pattern_matching_cases
    constraint_set
    pattern =
  let squelch_constraints =
    function_pattern_matching_cases
    |> Function_pattern_matching_case_set.enum
    |> Enum.map
      (
        fun (Function_pattern_matching_case (function_type, pattern)) ->
          Function_pattern_matching_constraint (
            Function_pattern_matching_constraint_squelch (
              function_type, pattern
            )
          )
      )
    |> Constraint_set.of_enum
  in

  function_pattern_matching_cases
  |> Function_pattern_matching_case_set.enum
  |> Enum.map
    (
      fun (
        Function_pattern_matching_case (
          (
            Function_type (
              parameter_type_variable,
              Constrained_type (
                return_type_variable,
                body_constraint_set
              )
            )
          ) as function_type,
          pattern
        )
      ) ->
        match pattern with
        (* FUNCTION MATCH and FUNCTION ANTI-MATCH *)
        (* These rules are almost identical, so they share most of the code. The only
           difference is in the kind of constraint that is generated, based on the
           consistency of the resulting constraint closure. *)
        | Function_pattern (
            parameter_pattern,
            return_pattern
          ) ->
          if not (
              Constraint_set.mem
                (
                  Function_pattern_matching_constraint (
                    Function_pattern_matching_constraint_squelch (
                      function_type,
                      pattern
                    )
                  )
                )
                constraint_set
            ) then
            let additional_constraints_to_test = Constraint_set.of_enum @@ List.enum [
                Lower_bound_constraint (
                  Restricted_type_lower_bound (
                    Restricted_type (
                      Unknown_type,
                      Type_restriction (
                        Positive_pattern_set (
                          Pattern_set.singleton parameter_pattern
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
              List.fold_left
                Constraint_set.union
                Constraint_set.empty
                [
                  constraint_set;
                  body_constraint_set;
                  additional_constraints_to_test;
                  squelch_constraints
                ]
            in
            logger `trace ("The constraint set being close over for function pattern search is: " ^ pretty_constraint_set constraint_set_to_test);
            let closed_constraint_set_to_test =
              perform_closure constraint_set_to_test
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
            Constraint_set.singleton (new_constraint)
          else
            Constraint_set.empty

        (* FORALL *)
        | Forall_pattern (
            old_pattern_variable,
            inner_pattern
          ) ->
          let new_pattern_variable =
            if Pattern_variable_map.mem old_pattern_variable !forall_consistent_freshness then
              Pattern_variable_map.find old_pattern_variable !forall_consistent_freshness
            else
              let fresh_pattern_variable = new_fresh_pattern_variable () in
              forall_consistent_freshness := Pattern_variable_map.add old_pattern_variable fresh_pattern_variable !forall_consistent_freshness;
              fresh_pattern_variable
          in
          let renamed_inner_pattern =
            rename_pattern_variable
              inner_pattern
              new_pattern_variable
              old_pattern_variable
          in
          function_pattern_search_ttype
            perform_closure
            (Function_type_type function_type)
            constraint_set
            renamed_inner_pattern
          |> Constraint_set.map
            (
              fun tconstraint ->
                match tconstraint with
                | Function_pattern_matching_constraint (
                    Function_pattern_matching_constraint_positive (
                      other_function_type,
                      subpattern
                    )
                  ) ->
                  if function_type = other_function_type then
                    Function_pattern_matching_constraint (
                      Function_pattern_matching_constraint_positive (
                        function_type,
                        Forall_pattern (
                          old_pattern_variable,
                          rename_pattern_variable
                            subpattern
                            old_pattern_variable
                            new_pattern_variable
                        )
                      )
                    )
                  else
                    raise @@ Invariant_failure "Different function types got into function_pattern_search and out of it."

                | Function_pattern_matching_constraint (
                    Function_pattern_matching_constraint_negative (
                      other_function_type,
                      subpattern
                    )
                  ) ->
                  if function_type = other_function_type then
                    Function_pattern_matching_constraint (
                      Function_pattern_matching_constraint_negative (
                        function_type,
                        Forall_pattern (
                          old_pattern_variable,
                          rename_pattern_variable
                            subpattern
                            old_pattern_variable
                            new_pattern_variable
                        )
                      )
                    )
                  else
                    raise @@ Invariant_failure "Different function types got into function_pattern_search and out of it."

                | _ ->
                  raise @@ Invariant_failure "Something different from a function pattern matching constraint got out of function_pattern_search."
            )

        | _ -> raise @@ Invariant_failure "Shouldn't consider function pattern matching case that's not either function or forall."
    )
  |> Enum.fold Constraint_set.union Constraint_set.empty
;;

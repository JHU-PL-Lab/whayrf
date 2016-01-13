open Batteries;;

open Whayrf_ast;;
open Whayrf_utils;;

type type_variable =
  | Type_variable of ident
;;

module Pattern_order =
struct
  type t = pattern
  let compare = compare
end;;

module Pattern_set = Set.Make(Pattern_order);;

type positive_pattern_set =
  | Positive_pattern_set of Pattern_set.t
;;

type negative_pattern_set =
  | Negative_pattern_set of Pattern_set.t
;;

type pattern_set =
  | Positive_pattern_set_pattern_set of positive_pattern_set
  | Negative_pattern_set_pattern_set of negative_pattern_set
;;

(* The following hack is necessary to have a type whose one of the variants
   refers to a set of one the other defined types. In particular, the constraint
   set is a set of constraints, which in turn are indirectly defined in terms of
   constraint sets.
*)
module type Types_basis =
sig
  type constraint_set
  and constrained_type =
    | Constrained_type of type_variable * constraint_set
  and lower_bound =
    | Restricted_type_lower_bound of restricted_type
    | Type_variable_lower_bound of type_variable
    | Application_lower_bound of type_variable * type_variable
    | Projection_lower_bound of type_variable * ident
    | Conditional_lower_bound of type_variable * pattern * function_type * function_type
  and tconstraint =
    | Lower_bound_constraint of lower_bound * type_variable
    | Type_variable_constraint of type_variable * pattern
    | Function_pattern_matching_constraint of function_pattern_matching_constraint
  and function_pattern_matching_constraint =
    | Function_pattern_matching_constraint_positive of function_type * pattern
    | Function_pattern_matching_constraint_negative of function_type * pattern
    | Function_pattern_matching_constraint_squelch of function_type * pattern
  and function_type =
    | Function_type of type_variable * constrained_type
  and ttype =
    | Record_type of type_variable Ident_map.t
    | Function_type_type of function_type
    | Unknown_type
  and type_restriction =
    | Type_restriction of positive_pattern_set * negative_pattern_set
  and restricted_type =
    | Restricted_type of ttype * type_restriction
end
;;

module rec Types : Types_basis with type constraint_set = Constraint_set.t =
  Types
and Constraint_order : Set.OrderedType =
struct
  type t = Types.tconstraint
  let compare = compare
end
and Constraint_set : (Set.S with type elt = Types.tconstraint) = Set.Make(Constraint_order);;

include Types;;

(** The function_type-pattern pair used in the main paper for ordering, cycle
    detection and returned by FUN PATS. *)
type function_pattern_matching_case = Function_pattern_matching_case of function_type * pattern;;

module Function_pattern_matching_case_order =
struct
  type t = function_pattern_matching_case
  let compare = compare
end
;;
module Function_pattern_matching_case_set = Set.Make(Function_pattern_matching_case_order);;

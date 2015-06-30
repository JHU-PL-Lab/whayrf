open Batteries;;

open Whayrf_ast;;
open Whayrf_ast_pretty;;
open Whayrf_ast_uid;;
open Whayrf_environment;;
open Whayrf_evaluation_failure;;

(**
   Value Compatibility.
*)
let rec is_compatible value environment pattern dispatch_table =
  (* LOOKUP is already performed when we get to this rule, since the parameter
     is already a value. This is made to have a sane API to `is_compatible'
     since values and variables are of different types. *)
  match (value, pattern) with
  (* RECORD *)
  | (
    Value_record(Record_value(record_elements)),
    Record_pattern(pattern_elements)
  ) ->
    pattern_elements
    |> Ident_map.enum
    |> Enum.for_all
      (
        fun (pattern_label, pattern_subpattern) ->
          record_elements
          |> Ident_map.enum
          |> Enum.exists
            (
              fun (record_label, record_subvariable) ->
                (pattern_label = record_label) &&
                (
                  (* Here is an example of where the LOOKUP rule is performed. *)
                  let record_subvalue = lookup environment record_subvariable in
                  is_compatible
                    record_subvalue
                    environment
                    pattern_subpattern
                    dispatch_table
                )
            )
      )

  (* FUNCTION *)
  | (Value_function(_), Function_pattern(_))

  (* FORALL *)
  | (_, Forall_pattern(_))

  (* EXISTS *)
  | (_, Pattern_variable_pattern(_)) ->
    dispatch_table value pattern

  (* Fallback *)
  | _ ->
    false
;;

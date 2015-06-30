open Batteries;;

open Whayrf_ast;;
open Whayrf_ast_pretty;;
open Whayrf_ast_uid;;
open Whayrf_environment;;
open Whayrf_evaluation_failure;;

let rec is_compatible value env pattern dispatch_table =
  match pattern with
  | Record_pattern(js) ->
    begin
      match value with
      | Value_record(Record_value(is)) ->
        Ident_map.fold (
          fun label pattern' result ->
            result &&
            Ident_map.mem label is &&
            let value' = lookup env @@ Ident_map.find label is in
            is_compatible value' env pattern' dispatch_table
        ) js true
      | Value_function(_) -> false
    end

  | Function_pattern(parameter_pattern, body_pattern) ->
    begin
      match value with
      | Value_record(_) -> false
      | Value_function(_) -> dispatch_table value pattern
    end

  | Pattern_variable_pattern(_)
  | Forall_pattern(_) ->
    dispatch_table value pattern
;;

open Batteries;;

open Whayrf_ast;;
open Whayrf_initial_alignment;;
open Whayrf_types;;
open Whayrf_types_pretty;;
open Whayrf_utils;;

(** Implements the Notation part that allows us to "project labels out of
    pattern sets".
*)
let project_pattern_set label pattern_set =
  pattern_set
  |> Pattern_set.enum
  |> Enum.filter_map (
    fun pattern ->
      match pattern with
      | Record_pattern (pattern_elements) ->
        if Ident_map.mem label pattern_elements then
          Some (Ident_map.find label pattern_elements)
        else
          None
      | _ -> raise @@ Invariant_failure "Tried to project label out of a non-record pattern."
  )
  |> Pattern_set.of_enum
;;

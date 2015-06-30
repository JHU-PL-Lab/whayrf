open Batteries;;

open Whayrf_ast;;
open Whayrf_string_utils;;

let pretty_ident (Ident s) = s;;

let pretty_freshening_stack (Freshening_stack ids) =
  List.fold_left
    (fun acc -> fun i ->
          (* Since freshening stacks are stored in reverse, we reverse the string    *)
          (* here.                                                                   *)
              acc ^ "__" ^ pretty_ident i) "" ids
;;

let pretty_var (Var(i, mfs)) =
  match mfs with
    | None -> pretty_ident i ^ "$"
    | Some fs -> pretty_ident i ^ pretty_freshening_stack fs
;;

let pretty_record_element (key, value) =
  (pretty_ident key) ^ " = " ^ (pretty_var value)
;;

let pretty_record_value (Record_value(is)) =
  is
  |> Ident_map.enum
  |> Enum.map pretty_record_element
  |> concat_sep_delim "{" "}" ", "
;;

let rec pretty_function_value (Function_value(x,e)) =
  pretty_var x ^ " -> { " ^ pretty_expr e ^ " }"

and pretty_value v =
  match v with
    | Value_record(r) -> pretty_record_value r
    | Value_function(f) -> pretty_function_value f

and pretty_clause_body b =
  match b with
    | Var_body(x) -> pretty_var x
    | Value_body(v) -> pretty_value v
    | Appl_body(x1,x2) -> pretty_var x1 ^ " " ^ pretty_var x2
    | Projection_body(x,l) -> pretty_var x ^ "." ^ pretty_ident l
    | Conditional_body(x,p,f1,f2) ->
        pretty_var x ^ " ~ " ^ pretty_pattern p ^ " ? " ^
        pretty_function_value f1 ^ " : " ^ pretty_function_value f2

and pretty_clause (Clause(x,b)) =
  pretty_var x ^ " = " ^ pretty_clause_body b

and pretty_expr (Expr(cls)) =
  concat_sep "; " @@ Enum.map pretty_clause @@ List.enum cls

and pretty_record_pattern_element (key, value) =
  (pretty_ident key) ^ " : " ^ (pretty_pattern value)

and pretty_pattern p =
  match p with
    | Record_pattern(is) ->
        concat_sep_delim "{" "}" ", " @@ Enum.map pretty_record_pattern_element @@
        Ident_map.enum is
    | Function_pattern(p1, p2) ->
      (pretty_pattern p1) ^ " ~> { " ^ (pretty_pattern p2) ^ " }"
    | Pattern_variable_pattern(pattern_variable) ->
      pretty_pattern_variable pattern_variable
    | Forall_pattern(pattern_variable, p) ->
      "forall " ^ (pretty_pattern_variable pattern_variable) ^ " . " ^ (pretty_pattern p)

and pretty_pattern_variable pattern_variable =
  match pattern_variable with
  | Pattern_variable (ident) ->
    pretty_ident ident
  | Fresh_pattern_variable (count) ->
    "__" ^ string_of_int count
;;

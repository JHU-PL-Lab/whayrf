open Batteries;;

open Whayrf_ast;;
open Whayrf_ast_pretty;;
open Whayrf_ast_uid;;

let logger = Whayrf_logger.make_logger "Whayrf_interpreter";;

module Environment = Var_hashtbl;;

let pretty_env (env : value Environment.t) =
  let inner =
    env
    |> Environment.enum
    |> Enum.map (fun (x,v) -> pretty_var x ^ " = " ^ pretty_value v)
    |> Enum.fold
        (fun acc -> fun s -> if acc = "" then s else acc ^ ", " ^ s) ""
  in
  "{ " ^ inner ^ " }"
  ;;

exception Evaluation_failure of string;;

let lookup env x =
  if Environment.mem env x then
    Environment.find env x
  else
    raise (
        Evaluation_failure (
          "cannot find variable `" ^ (pretty_var x) ^ "' in environment `" ^ (pretty_env env) ^ "'."
        )
      )
;;

let bound_vars_of_expr (Expr(cls)) =
  cls
  |> List.map (fun (Clause(x, _)) -> x)
  |> Var_set.of_list
;;

let rec var_replace_expr fn (Expr(cls)) =
  Expr(List.map (var_replace_clause fn) cls)

and var_replace_clause fn (Clause(x, b)) =
  Clause(fn x, var_replace_clause_body fn b)

and var_replace_clause_body fn r =
  match r with
  | Value_body(v) -> Value_body(var_replace_value fn v)
  | Var_body(x) -> Var_body(fn x)
  | Appl_body(x1, x2) -> Appl_body(fn x1, fn x2)
  | Projection_body(x,l) -> Projection_body(fn x, l)
  | Conditional_body(x,p,f1,f2) ->
      Conditional_body(fn x, p, var_replace_function_value fn f1,
        var_replace_function_value fn f2)

and var_replace_value fn v =
  match v with
  | Value_record(r) ->
    Value_record(var_replace_record_value fn r)
  | Value_function(f) -> Value_function(var_replace_function_value fn f)

and var_replace_record_value fn (Record_value r) =
  Record_value(
    r
    |> Ident_hashtbl.enum
    |> Enum.map (
      fun (k, v) ->
        (k, fn v)
    )
    |> Ident_hashtbl.of_enum
  )

and var_replace_function_value fn (Function_value(x, e)) =
  Function_value(fn x, var_replace_expr fn e)
      
let freshening_stack_from_var x =
  let Var(appl_i, appl_fso) = x in
  (* The freshening stack of a call site at top level is always
     present. *)
  let Freshening_stack idents = Option.get appl_fso in
  Freshening_stack (appl_i :: idents)
  ;;

let repl_fn_for clauses freshening_stack extra_bound =
  let bound_variables =
    clauses
    |> List.map (fun (Clause(x, _)) -> x)
    |> Var_set.of_list
    |> Var_set.union extra_bound 
  in
  let repl_fn (Var(i, fso) as x) =
    if Var_set.mem x bound_variables
      then Var(i, Some freshening_stack)
      else x
  in
  repl_fn
;;

let fresh_wire (Function_value(param_x, Expr(body))) arg_x call_site_x =
  (* Build the variable freshening function. *)
  let freshening_stack = freshening_stack_from_var call_site_x in
  let repl_fn =
      repl_fn_for body freshening_stack @@ Var_set.singleton param_x in
  (* Create the freshened, wired body. *)
  let freshened_body = List.map (var_replace_clause repl_fn) body in
  let head_clause = Clause(repl_fn param_x, Var_body(arg_x)) in
  let Clause(last_var, _) = List.last freshened_body in
  let tail_clause = Clause(call_site_x, Var_body(last_var)) in
  [head_clause] @ freshened_body @ [tail_clause]
;;

let rec is_compatible value env pattern dispatch_table =
  match pattern with
  | Record_pattern(js) ->
    begin
      match value with
      | Value_record(Record_value(is)) ->
        Ident_hashtbl.fold (
          fun label pattern' result ->
            result &&
            Ident_hashtbl.mem is label &&
            let value' = lookup env @@ Ident_hashtbl.find is label in
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

let rec evaluate env lastvar cls =
  logger `debug (
      pretty_env env ^ "\n" ^
      (Option.default "?" (Option.map pretty_var lastvar)) ^ "\n" ^
      (cls
       |> List.map pretty_clause
       |> List.fold_left (fun acc -> fun s -> acc ^ s ^ "; ") "") ^ "\n\n");
  flush stdout;
  match cls with
  | [] ->
      begin
        match lastvar with
        | Some(x) -> (x, env)
        | None ->
        (* TODO: different exception? *)
            raise (Failure "evaluation of empty expression!")
      end
  | (Clause(x, b)):: t ->
      match b with
      | Value_body(v) ->
          Environment.add env x v;
          evaluate env (Some x) t
      | Var_body(x') ->
          let v = lookup env x' in
          Environment.add env x v;
          evaluate env (Some x) t
      | Appl_body(x', x'') ->
          begin
            match lookup env x' with
              | Value_record(_) as r -> raise (Evaluation_failure
                  ("cannot apply " ^ pretty_var x' ^
                    " as it contains non-function " ^ pretty_value r))
              | Value_function(f) ->
                  evaluate env (Some x) @@ fresh_wire f x'' x @ t
          end
      | Projection_body(x',l) ->
          begin
            match lookup env x' with
            | Value_record(Record_value(r)) as value_record ->
              if Ident_hashtbl.mem r l then
                let v = lookup env @@ Ident_hashtbl.find r l in
                Environment.add env x v;
                evaluate env (Some x) t
              else
                raise (Evaluation_failure
                  ("cannot find label " ^ pretty_ident l ^
                   " in variable " ^ pretty_var x' ^
                   " that contains record " ^ pretty_value value_record))
            | Value_function(_) as f -> raise (Evaluation_failure
                                                 ("cannot select " ^ pretty_var x' ^
                                                  " as it contains non-record " ^ pretty_value f))
          end
      | Conditional_body(x',p,f1,f2) ->
        (* TODO: The first pass of implementation is ignoring the dispatch
                 table, because we need the type system to make it work and the
                 type system doesn't exist yet. We're always failing to match,
                 which is a good default because we're always failing to produce
                 a proof (that's bad but not incorrect). We need to come back
                 here and implement this right. *)
        let successful_match = is_compatible (lookup env x') env p (fun value pattern -> false) in
        let f_target = if successful_match then f1 else f2 in
        evaluate env (Some x) @@ fresh_wire f_target x' x @ t            
;;

let eval (Expr(cls)) =
  let env = Environment.create(20) in
  let repl_fn = repl_fn_for cls (Freshening_stack []) Var_set.empty in
  let cls' = List.map (var_replace_clause repl_fn) cls in
  evaluate env None cls'
;;

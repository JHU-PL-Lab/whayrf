open Batteries;;

open Whayrf_ast;;
open Whayrf_ast_pretty;;
open Whayrf_ast_uid;;
open Whayrf_environment;;
open Whayrf_evaluation_failure;;
open Whayrf_value_compatibility;;

let logger = Whayrf_logger.make_logger "Whayrf_interpreter";;

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
  Record_value(Ident_map.map fn r)

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

(** Inner implementation of evaluation. Not meant to be directly called. *)
let rec evaluate env lastvar cls dispatch_table =
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

      (* This rule is not on the relation, its job is to skip over clauses that
         are ready to going to go to the environment. *)
      | Value_body(v) ->
          Environment.add env x v;
          evaluate env (Some x) t dispatch_table

      (* VARIABLE LOOKUP *)
      | Var_body(x') ->
          let v = lookup env x' in
          Environment.add env x v;
          evaluate env (Some x) t dispatch_table

      (* PROJECTION *)
      | Projection_body(x',l) ->
          begin
            match lookup env x' with
            | Value_record(Record_value(r)) as value_record ->
              if Ident_map.mem l r then
                let v = lookup env @@ Ident_map.find l r in
                Environment.add env x v;
                evaluate env (Some x) t dispatch_table
              else
                raise (Evaluation_failure
                  ("cannot find label " ^ pretty_ident l ^
                   " in variable " ^ pretty_var x' ^
                   " that contains record " ^ pretty_value value_record))
            | Value_function(_) as f -> raise (Evaluation_failure
                                                 ("cannot select " ^ pretty_var x' ^
                                                  " as it contains non-record " ^ pretty_value f))
          end

      (* APPLICATION *)
      | Appl_body(x', x'') ->
          begin
            match lookup env x' with
              | Value_record(_) as r -> raise (Evaluation_failure
                  ("cannot apply " ^ pretty_var x' ^
                    " as it contains non-function " ^ pretty_value r))
              | Value_function(f) ->
                  evaluate env (Some x) (fresh_wire f x'' x @ t) dispatch_table
          end

      (* CONDITIONAL SUCCESS and CONDITIONAL FAILURE *)
      | Conditional_body(x',p,f1,f2) ->
        let successful_match = is_compatible (lookup env x') env p dispatch_table in
        let f_target = if successful_match then f1 else f2 in
        evaluate env (Some x) (fresh_wire f_target x' x @ t) dispatch_table
;;

(** Façade for evaluation.

    Not a single step of the Small Step Operation Semantics (->^1), but the
    fixpoint that performs every operation available. *)
let eval (Expr(cls)) dispatch_table =
  let env = Environment.create(20) in
  let repl_fn = repl_fn_for cls (Freshening_stack []) Var_set.empty in
  let cls' = List.map (var_replace_clause repl_fn) cls in
  evaluate env None cls' dispatch_table
;;

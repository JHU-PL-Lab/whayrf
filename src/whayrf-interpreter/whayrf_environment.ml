open Batteries;;

open Whayrf_ast;;
open Whayrf_ast_pretty;;
open Whayrf_ast_uid;;
open Whayrf_evaluation_failure;;

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

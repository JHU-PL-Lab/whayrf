open Batteries;;

let fresh_var_counter = ref 0;;

let fresh_var () =
  let index = !fresh_var_counter in
  fresh_var_counter := !fresh_var_counter + 1;
  let name = "a__" ^ (string_of_int index) in
  Whayrf_ast.Var(Whayrf_ast.Ident(name),None)
;;

let rec pattern_of_nested_pattern p =
  match p with
    | Whayrf_nested_ast.Record_pattern idents ->
        Whayrf_ast.Record_pattern idents
;;

let rec function_value_of_nested_function_value
    (Whayrf_nested_ast.Function(x',e')) =
  let (body,_) = clauses_and_var_of_nested_expr e' in
  Whayrf_ast.Function_value(x',Whayrf_ast.Expr body)

and clauses_and_var_of_nested_expr e =
  let x = fresh_var() in
  let (clauses,final_body) =
    match e with
      | Whayrf_nested_ast.Record_expr idents ->
          ([], Whayrf_ast.Value_body(
                  Whayrf_ast.Value_record(
                    Whayrf_ast.Record_value idents)))
      | Whayrf_nested_ast.Function_expr(f) ->
          ([], Whayrf_ast.Value_body(
                  Whayrf_ast.Value_function(
                    function_value_of_nested_function_value f)))
      | Whayrf_nested_ast.Var_expr(x') ->
          ([], Whayrf_ast.Var_body(x'))
      | Whayrf_nested_ast.Appl_expr(e1,e2) ->
          let (cls1,x1) = clauses_and_var_of_nested_expr e1 in
          let (cls2,x2) = clauses_and_var_of_nested_expr e2 in
          (cls1 @ cls2, Whayrf_ast.Appl_body(x1,x2))
      | Whayrf_nested_ast.Conditional_expr(e',p,f1,f2) ->
          let (cls0,x') = clauses_and_var_of_nested_expr e' in
          ( cls0
          , Whayrf_ast.Conditional_body(
              x', pattern_of_nested_pattern p,
              function_value_of_nested_function_value f1,
              function_value_of_nested_function_value f2))
      | Whayrf_nested_ast.Let_expr(x',e1,e2) ->
          let (cls1,x1) = clauses_and_var_of_nested_expr e1 in
          let (cls2,x2) = clauses_and_var_of_nested_expr e2 in
          ( cls1 @
            [ Whayrf_ast.Clause(x', Whayrf_ast.Var_body(x1)) ] @
            cls2
          , Whayrf_ast.Var_body(x2)
          )
  in
  (clauses @ [Whayrf_ast.Clause(x,final_body)],x)

let a_translate_whayrf_nested_expr e =
  let (cls,_) = clauses_and_var_of_nested_expr e in
  Whayrf_ast.Expr cls
;;

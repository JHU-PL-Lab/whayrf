(**
  A front-end for the LittleBang parser library.
*)

open Batteries;;

open Whayrf_nested_ast;;
open Whayrf_nested_generated_lexer;;
open Whayrf_nested_generated_parser;;

let parse_whayrf_expressions (input : IO.input) =
  let buf = Lexing.from_input input in
  let read_expr () =
    Whayrf_nested_generated_parser.delim_expr Whayrf_nested_generated_lexer.token buf
  in
  LazyList.from_while read_expr;;

let parse_whayrf_program (input : IO.input) =
  let buf = Lexing.from_input input in
  Whayrf_nested_generated_parser.prog Whayrf_nested_generated_lexer.token buf
;;

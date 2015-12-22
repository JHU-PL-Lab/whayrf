{
  open Whayrf_parser_support;;
  open Whayrf_generated_parser;;
}

let digit = ['0'-'9']
let alpha = ['a'-'z'] | ['A'-'Z'] | '_'
let whitespace = [' ' '\t' '\n']
let comment = '#' [^'\n']* '\n'

let ident_start = alpha
let ident_cont = alpha | digit

rule token = parse
  | eof                              { EOF }
  | comment                          { token lexbuf }
  | whitespace                       { token lexbuf }
  | "{"                              { OPEN_BRACE }
  | "}"                              { CLOSE_BRACE }
  | ";"                              { SEMICOLON }
  | ","                              { COMMA }
  | "="                              { EQUALS }
  | "->"                             { ARROW }
  | "~>"                             { TILDE_ARROW }
  | "?"                              { QUESTION_MARK }
  | "~"                              { TILDE }
  | ":"                              { COLON }
  | "."                              { DOT }
  | "fun"                            { KEYWORD_FUN }
  | "forall"                         { KEYWORD_FORALL }
  | ident_start ident_cont* as s     { IDENTIFIER s }
  | ";;"                             { DOUBLE_SEMICOLON }

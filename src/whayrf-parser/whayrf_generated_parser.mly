%{
open Whayrf_ast;;
open Whayrf_ast_uid;;
open Whayrf_parser_support;;
open Whayrf_source_origin;;
open Lexing;;
%}

%token <string> IDENTIFIER
%token EOF 
%token OPEN_BRACE 
%token CLOSE_BRACE 
%token SEMICOLON
%token COMMA
%token EQUALS 
%token ARROW 
%token TILDE_ARROW 
%token QUESTION_MARK 
%token TILDE 
%token COLON 
%token DOT 
%token KEYWORD_FUN 
%token DOUBLE_SEMICOLON 

%start <Whayrf_ast.expr> prog
%start <Whayrf_ast.expr option> delim_expr

%%

prog:
  | expr EOF
      { $1 }
  ;
  
delim_expr:
  | EOF
      { None }
  | expr DOUBLE_SEMICOLON
      { Some($1) }
  | expr EOF
      { Some($1) }
  ;

expr:
  | separated_nonempty_trailing_list(SEMICOLON, clause)
      { Expr($1) }
  ;

clause:
  | variable EQUALS clause_body
      { Clause($1,$3) }
  ;

variable:
  | identifier
      { Var($1,None) }
  ;
  
identifier:
  | IDENTIFIER
      { Ident $1 }
  ;

clause_body:
  | value
      { Value_body($1) }
  | variable
      { Var_body($1) }
  | variable variable
      { Appl_body($1,$2) }
  | variable DOT identifier
      { Projection_body($1,$3) }
  | variable TILDE pattern QUESTION_MARK variable ARROW OPEN_BRACE expr CLOSE_BRACE COLON variable ARROW OPEN_BRACE expr CLOSE_BRACE
      { Conditional_body($1,$3,Function_value($5,$8),Function_value($11,$14)) }
  ;

value:
  | record_value
      { Value_record($1) }
  | function_value
      { Value_function($1) }
  ;

record_element:
  | identifier EQUALS variable
      { ($1,$3) }
  ;

record_value:
  | OPEN_BRACE CLOSE_BRACE
      { Record_value(Ident_map.empty) }
  | OPEN_BRACE separated_nonempty_trailing_list(COMMA, record_element) CLOSE_BRACE
      { Record_value(Ident_map.of_enum (Batteries.List.enum $2)) }
  ;
  
function_value:
  | KEYWORD_FUN variable ARROW OPEN_BRACE expr CLOSE_BRACE
      { Function_value($2,$5) }
  ;

record_pattern_element:
  | identifier COLON pattern
      { ($1,$3) }
  ;

pattern:
  | OPEN_BRACE CLOSE_BRACE
      { Record_pattern(Ident_map.empty) }
  | OPEN_BRACE separated_nonempty_trailing_list(COMMA, record_pattern_element) CLOSE_BRACE
      { Record_pattern(Ident_map.of_enum (Batteries.List.enum $2)) }
  | KEYWORD_FUN pattern TILDE_ARROW OPEN_BRACE pattern CLOSE_BRACE
      { Function_pattern($2,$5) }
  ;

separated_nonempty_trailing_list(separator, rule):
  | nonempty_list(terminated(rule, separator))
      { $1 }
  | separated_nonempty_list(separator,rule)
      { $1 }
  ;

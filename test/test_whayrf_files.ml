(**
  This test module will load a series of test files from the test sources
  directory and execute them one by one.
  
  Each file is expected to contain a comment describing the expected test
  result.  The comment should be of one of the following forms:
  
    - [EXPECT-EVALUATE] (which requires that the code evaluates to completion)
    - [EXPECT-STUCK] (which requires that the code gets stuck)
    - [EXPECT-TYPECHECK] (which requires that the code typechecks)
    - [EXPECT-TYPEFAIL] (which requires that the code fails to typecheck)
*)

open Batteries;;
open OUnit2;;

open Whayrf_ast_wellformedness;;
open Whayrf_evaluation_failure;;
open Whayrf_interpreter;;
open Whayrf_parser;;
open Whayrf_typechecker;;
open Whayrf_utils;;

exception File_test_creation_failure of string;;

type test_expectation =
  | Expect_evaluate
  | Expect_stuck
  | Expect_typecheck
  | Expect_typefail
  | Expect_illformed
;;

let parse_expectation str =
  match str with
    | "EXPECT-EVALUATE" -> Some(Expect_evaluate)
    | "EXPECT-STUCK" -> Some(Expect_stuck)
    | "EXPECT-TYPECHECK" -> Some(Expect_typecheck)
    | "EXPECT-TYPEFAIL" -> Some(Expect_typefail)
    | "EXPECT-ILLFORMED" -> Some(Expect_illformed)
    | _ -> None
;;

let make_test filename expectations =
  (* Begin by parsing the file. *)
  let expr = File.with_file_in filename Whayrf_parser.parse_whayrf_program in
  (* Verify that it is well-formed. *)
  let well_formed =
    try
      check_wellformed_expr expr;
      true
    with
    | Illformedness_found _ -> false
  in
  (* Next, typecheck it. *)
  let (typecheck_result, dispatch_table) =
    if well_formed then
      typecheck expr
    else
      (false, fun _ _ -> false)
  in
  let make_single_test expectation =
    let test_name_expectation = match expectation with
      | Expect_evaluate ->
        "(should evaluate)"
      | Expect_stuck ->
        "(should get stuck)"
      | Expect_typecheck ->
        "(should get typecheck)"
      | Expect_typefail ->
        "(should fail to typecheck)"
      | Expect_illformed ->
        "(should be illformed)"
    in
    let test_name = filename ^ ": " ^ test_name_expectation in
    (* Create the test in a thunk. *)
    test_name >::
    function _ ->
      (* Now, based on our expectation, do the right thing. *)
      match expectation with
      | Expect_evaluate ->
        begin
          try
            ignore @@ eval expr dispatch_table
          with Evaluation_failure(failure) ->
            assert_failure @@ "Evaluation became stuck: " ^ failure
        end
      | Expect_stuck ->
        begin
          try
            ignore (eval expr dispatch_table);
            assert_failure ("Evaluation completed")                
          with Evaluation_failure(failure) ->
            ()
        end
      | Expect_typecheck ->
        assert_bool "Typechecking failed." typecheck_result
      | Expect_typefail ->
        assert_bool "Typechecking succeeded." @@ not typecheck_result
      | Expect_illformed ->
        assert_bool "The program is well formed." @@ not well_formed
  in
  List.map make_single_test expectations
;;

let make_test_from filename =
  let expectations =
    filename
      |> File.lines_of
      |> Enum.filter_map
          (fun str ->
            let str' = String.trim str in
            if String.starts_with str' "#"
              then
                let str'' = String.trim @@ String.tail str' 1 in
                parse_expectation str''
              else None
          )
      |> List.of_enum
  in
  match expectations with
    | [] ->
        raise (File_test_creation_failure(
          "Could not create test from file " ^ filename ^
          ": no expectation comment found."))
    | _ ->
      List.enum @@ make_test filename expectations
;;

let make_all_tests pathname =
  if Sys.file_exists pathname && Sys.is_directory pathname
    then
      Sys.files_of pathname
        |> Enum.map (fun f -> pathname ^ Filename.dir_sep ^ f)
        |> Enum.filter (fun f -> not @@ Sys.is_directory f)
        |> Enum.filter (fun f -> String.ends_with f ".whayrf")
        |> Enum.map make_test_from
        |> Enum.concat
        |> List.of_enum
    else
      raise (File_test_creation_failure(
        "Test file directory " ^ pathname ^ " is missing"))
;;

let tests = "Test_whayrf_files" >::: make_all_tests "test-sources";;

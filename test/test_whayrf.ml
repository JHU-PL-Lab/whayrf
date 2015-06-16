open OUnit2

let all_tests =
  [ Test_whayrf_utils.tests
  ; Test_whayrf_files.tests
  ];;

run_test_tt_main ("Whayrf" >::: all_tests);;

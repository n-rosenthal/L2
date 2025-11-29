open Interpreter
open Terms
open Testing

let all_tests =
  integers @ booleans @ conditionals @ 
  binary_operations @ programs
;;


let _ =
  List.iteri
    (fun i e ->
       print_int i;
       print_string ". ";
       print_endline "------------------------------------";
       interpreter e;
       print_endline "")
    all_tests
;;

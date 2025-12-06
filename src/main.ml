open Interpreter
open Terms
open Types
open Testing



let () =                            
  List.iteri
    (fun i e ->
        print_endline ("Teste " ^ string_of_int (i + 1));
        interpret e;
        print_endline "")
    Testing.all_tests


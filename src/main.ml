open Interpreter
open Terms
open Types
open Testing

(** testes para memória **)

(** identificador ou variável x *)
let var_x = (Let (Identifier "x", Int, Integer 1,
                Conditional (Boolean true,
                            Dereference (Identifier "x"),
                            Integer 2)));;
let all_tests = [
  var_x
];;

let () =
  List.iteri
    (fun i e ->
        print_int i;
        print_string ". ";
        print_endline "------------------------------------";
        interpret e;
        print_endline "")
    all_tests


open Interpreter
open Terms
open Types
open Testing

(** testes para memória **)

(** identificador ou variável x *)

(** 
  let x : Int = -1 in
    let y : Int = 1 in
      !x + !y 
*)
let sum a b = (Let ("x", Int, Integer a, Let ("y", Int, Integer b, 
              (BinaryOperation (
                Add,
                Dereference (Identifier "x"),
                Dereference (Identifier "y")
              )))))
let all_tests = [
  sum 1 2
];;

let () =
  List.iteri
    (fun i e ->
        print_endline ("Teste " ^ string_of_int (i + 1));
        interpret e;
        print_endline "")
    all_tests


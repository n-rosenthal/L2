open Interpreter
open Terms
open Types
open Testing

(** testes para memória **)

(** identificador ou variável x *)

        (**      TESTE - fatorial      

            let  x: int     =  5 in 
            let  z: ref int = new x in 
            let  y: ref int = new 1 in 
            
            (while (!z > 0) (
                    y :=  !y * !z;
                    z :=  !z - 1);
            ! y)
        *)
let fat n = Let ("x", Int, Integer n,
              Let ("y", Reference Int, New (Identifier "x"),
                  Let ("z", Reference Int, New (Integer 1),
                      Sequence (
                        While (
                          BinaryOperation (Gt, Dereference (Identifier "z"), Integer 0),
                          Sequence (
                            Assignment (
                              Identifier "y",
                              BinaryOperation (Mul, Dereference (Identifier "y"), Dereference (Identifier "z"))
                            ),
                            Assignment (
                              Identifier "z",
                              BinaryOperation (Sub, Dereference (Identifier "z"), Integer 1))
                          )
                        ),
                        Dereference (Identifier "y")
                      )
                  )))
;;

let () =                            
  List.iteri
    (fun i e ->
        print_endline ("Teste " ^ string_of_int (i + 1));
        interpret e;
        print_endline "")
    [fat 5]


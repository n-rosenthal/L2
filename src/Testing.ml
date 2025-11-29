(**
    `src/Testing.ml`
    
    Testes unitários para o interpretador de L2
*)

open Types
open Terms
open TypeInference
open Evaluation


let assert_tipo (e: term) (t: tipo) : bool = eq_tipo (typeinfer e []) t;;
let assert_value (e: term) (v: value) : bool = (match value_of_term e with
    | Some v' -> v = v'
    | None -> false
);;
let assert_equal (e1: term) (e2: term) : bool = e1 = e2;;

(** testes *)
let integers: term list = [
  Integer 1; Integer (-1); Integer 0; Integer ((-1) + (-1));
];;

let booleans: term list = [
  Boolean true; Boolean false;
];;

let values: term list = integers @ booleans @ [Unit];;

let conditionals: term list = [
  Conditional (Boolean true, Integer 1, Integer 2);
  Conditional (Boolean false, Integer 1, Integer 2);

  (** erro e1 !: Bool *)
  Conditional (Integer 1, Integer 1, Integer 2);
  Conditional (Integer 1, Boolean true, Boolean false);

  (** erro e2: t, e3: t', t <> t' *)
  Conditional (Boolean true, Integer 1, Boolean false);
];;

let binary_operations: term list = [
  (** op. binárias aritméticas *)
  BinaryOperation (Add, Integer 1, Integer 2);
  BinaryOperation (Sub, Integer 1, Integer 2);
  BinaryOperation (Mul, Integer 1, Integer 2);
  BinaryOperation (Div, Integer 1, Integer 2);

  (** erro n2 = 0 em (div, n1, n2) *)
  BinaryOperation (Div, Integer 1, Integer 0);

  (** op. binárias aritméticas relacionais *)
  BinaryOperation (Eq, Integer 1, Integer 2);
  BinaryOperation (Neq, Integer 1, Integer 2);
  BinaryOperation (Lt, Integer 1, Integer 2);
  BinaryOperation (Leq, Integer 1, Integer 2);

  (** op. binárias lógicas *)
  BinaryOperation (And, Boolean true, Boolean false);
  BinaryOperation (Or, Boolean true, Boolean false);

  (** erro op. binário inválido *)
  BinaryOperation (Add, Boolean true, Boolean false);
];;
        (**      TESTE - fatorial      

            let  x: int     =  5 in 
            let  z: ref int = new x in 
            let  y: ref int = new 1 in 
            
            (while (!z > 0) (
                    y :=  !y * !z;
                    z :=  !z - 1);
            ! y)
        *)

        let fatorial : term = 
          Let ("x", Int, Integer 5,
            Let ("z", Reference Int, New (Identifier "x"),
              Let ("y", Reference Int, New (Integer 1),
                Sequence (
                  While (
                    BinaryOperation
                      (Gt,
                        Derefence (Identifier "z"),
                        Integer 0),
        
                    Sequence (
                      Assignment (
                        Identifier "y",
                        BinaryOperation
                          (Mul,
                            Derefence (Identifier "y"),
                            Derefence (Identifier "z"))
                      ),
        
                      Assignment (
                        Identifier "z",
                        BinaryOperation
                          (Sub,
                            Derefence (Identifier "z"),
                            Integer 1))
                    )
                  ),
        
                  Derefence (Identifier "y")
                )
              )
            )
          )
        ;;
        

let programs: term list = [
  fatorial;
];

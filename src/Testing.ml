(**
    `src/Testing.ml`
    
    Testes unitários para o interpretador de L2
*)

open Types          (*  tipos da linguagem `L2` *)
open Terms          (*  sintaxe de termos sobre `L2` *)
open TypeInference  (*  inferência estática de tipos para `L2` *)
open Evaluation     (*  avaliação de termos para `L2` *)

(** testes para valores *)
let values_tests = [
  Integer 1; Integer (-1);
  Boolean true; Boolean false;
  (* Location 10; Location (-10); -> stack_overflow *)
  Unit;
]

(** if *)
  let if_tests = [
    Conditional (Boolean true,  Integer 1, Integer 0);
    Conditional (Boolean false, Integer 1, Integer 0);
    Conditional (Integer 1,     Integer 1, Integer 0);   (* erro *)
    Conditional (Integer (-1),  Integer 1, Integer 0);   (* erro *)
  ]

(** operações binárias *)
let binop_tests = [
  BinaryOperation (Add, Integer 1, Integer 2);
  BinaryOperation (Sub, Integer 1, Integer 2);
  BinaryOperation (Mul, Integer 1, Integer 2);
  BinaryOperation (Div, Integer 1, Integer 2);
  BinaryOperation (Div, Integer 1, Integer 0); (** erro *)
  BinaryOperation (Eq, Integer 1, Integer 2);
  BinaryOperation (Neq, Integer 1, Integer 2);
  BinaryOperation (Gt, Integer 1, Integer 2);
  BinaryOperation (Geq, Integer 1, Integer 2);
  BinaryOperation (Lt, Integer 1, Integer 2);
  BinaryOperation (Leq, Integer 1, Integer 2);
  BinaryOperation (And, Boolean true, Boolean false);
  BinaryOperation (Or, Boolean true, Boolean false);
]
let fatorial n =
  Let ("x", Int, Integer n,
    Let ("y", Reference Int, New (Integer 1),
      Let ("z", Reference Int, New (Identifier "x"),
        Sequence (
          While (
            BinaryOperation (Gt, Dereference (Identifier "z"), Integer 0),
            Sequence (
              Assignment (
                Identifier "y",
                BinaryOperation (Mul,
                  Dereference (Identifier "y"),
                  Dereference (Identifier "z"))
              ),
              Assignment (
                Identifier "z",
                BinaryOperation (Sub,
                  Dereference (Identifier "z"),
                  Integer 1))
            )
          ),
          Dereference (Identifier "y")
        )
      )
    )
  )

  (**
  gcd(a, b) usando o algoritmo:

  while b != 0:
      tmp = b
      b = a mod b
      a = tmp
  return a
*)

let gcd_term a b =
  Let ("a", Int, Integer a,
    Let ("b", Int, Integer b,

      (* criar referências de trabalho *)
      Let ("x", Reference Int, New (Identifier "a"),
      Let ("y", Reference Int, New (Identifier "b"),

        (* while !y != 0: *)
        Sequence (
          While (
            BinaryOperation (Neq,
              Dereference (Identifier "y"),
              Integer 0),

            (* corpo: tmp := !y; y := !x mod !y; x := tmp *)
            Sequence (

              (* tmp := !y; y := ...; x := tmp *)
              Let ("tmp", Reference Int,
                New (Dereference (Identifier "y")),
                Sequence (

                  (* y := !x mod !y *)
                  Assignment (
                    Identifier "y",
                    BinaryOperation (Mod,
                      Dereference (Identifier "x"),
                      Dereference (Identifier "y"))
                  ),

                  (* x := !tmp *)
                  Assignment (
                    Identifier "x",
                    Dereference (Identifier "tmp")
                  )
                )
              ),

              (* segundo argumento obrigatório do Sequence *)
              Unit
            )
          ),

          (* return !x *)
          Dereference (Identifier "x")
        )
      )))
  )
(* Soma 1 + 2 + ... + n *)
let sum_to n =
  Let ("n", Int, Integer n,
    Let ("acc", Reference Int, New (Integer 0),
    Let ("i", Reference Int, New (Integer 1),
      Sequence (
        While (
          BinaryOperation (Leq, Dereference (Identifier "i"), Identifier "n"),
          Sequence (
            Assignment (
              Identifier "acc",
              BinaryOperation (Add,
                Dereference (Identifier "acc"),
                Dereference (Identifier "i"))
            ),
            Assignment (
              Identifier "i",
              BinaryOperation (Add,
                Dereference (Identifier "i"),
                Integer 1)
            )
          )
        ),
        Dereference (Identifier "acc")
      )
    )))

(* Par ou ímpar *)
let is_even n =
  Conditional (
    BinaryOperation (Eq,
      BinaryOperation (Mod, Integer n, Integer 2),
      Integer 0),
    Boolean true,
    Boolean false
  )

(* Potência: a^b *)
let pow a b =
  Let ("a", Reference Int, New (Integer a),
  Let ("b", Reference Int, New (Integer b),
  Let ("acc", Reference Int, New (Integer 1),

    Sequence (

      While (
        BinaryOperation (Gt,
          Dereference (Identifier "b"),
          Integer 0
        ),

        Sequence (
          Assignment (
            Identifier "acc",
            BinaryOperation (Mul,
              Dereference (Identifier "acc"),
              Dereference (Identifier "a")
            )
          ),

          Sequence (
            Assignment (
              Identifier "b",
              BinaryOperation (Sub,
                Dereference (Identifier "b"),
                Integer 1
              )
            ),
            Unit
          )
        )
      ),

      Dereference (Identifier "acc")
    )

  )))

(**
  let x : int = 10 in
  let y : int = 0 in 
    (while ( x > y ) do
      x := !x - 1;
      y := !y + 1
    );
    
    !y)
*)
let counter : term = 
  Let ("x", Reference Int, New (Integer 10),  (* x é ref int *)
    Let ("y", Reference Int, New (Integer 0),  (* y é ref int *)
      Sequence (
        While (
          BinaryOperation (Gt, Dereference (Identifier "x"), Dereference (Identifier "y")),
          Sequence (
            Assignment (Identifier "x", 
              BinaryOperation (Sub, Dereference (Identifier "x"), Integer 1)),
            Assignment (Identifier "y",
              BinaryOperation (Add, Dereference (Identifier "y"), Integer 1))
          )
        ),
        Dereference (Identifier "y")
      )
    )
  )

(**
  let dividendo : Int = a in
  let divisor   : Int = b in
  let resto     : Int Ref = dividendo in
    (while ( resto >= divisor ) do
      resto := !resto - divisor
    );
    !resto
*)
let modulo (a: int) (b: int) : term = 
  Let ("dividendo", Int, Integer a,
    Let ("divisor", Int, Integer b,
      Let ("resto", Reference Int, New (Identifier "dividendo"),
        Sequence (
          While (
            BinaryOperation (Geq, Dereference (Identifier "resto"), Identifier "divisor"),
            Assignment (
              Identifier "resto",
              BinaryOperation (Sub, 
                Dereference (Identifier "resto"), 
                Identifier "divisor"
              )
            )
          ),
          Dereference (Identifier "resto")
        )
      )
    )
  )

let a_tests = [
  fatorial 5;
  gcd_term 30 18;   (* gcd(30,18) = 6 *)
  gcd_term 42 12;   (* gcd(42,12) = 6 *)
  gcd_term 17 13;   (* gcd(17,13) = 1 *)
  sum_to 10;
  pow 2 8;          (* 256 *)
  is_even 7;
  is_even 12;
]

let all_tests =
  [counter ; modulo 10 3]

(**
    `src/Testing.ml`
    
    Testes unitários para o interpretador de L2
*)

open Types          (*  tipos da linguagem `L2` *)
open Terms          (*  sintaxe de termos sobre `L2` *)
open TypeInference  (*  inferência estática de tipos para `L2` *)
open Evaluation     (*  avaliação de termos para `L2` *)






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
                      Dereference (Identifier "z"),
                        Integer 0),
        
                    Sequence (
                      Assignment (
                        Identifier "y",
                        BinaryOperation
                          (Mul,
                          Dereference (Identifier "y"),
                          Dereference (Identifier "z"))
                      ),
        
                      Assignment (
                        Identifier "z",
                        BinaryOperation
                          (Sub,
                          Dereference (Identifier "z"),
                            Integer 1))
                    )
                  ),
        
                  Dereference (Identifier "y")
                )
              )
            )
          )
        ;;
        

(**
    let cndwhi = Binop(Gt, Deref (Id "z"),Num 0)
let asgny = Asg(Id "y", Binop(Mul, Deref (Id "y"),Deref(Id "z")))
let asgnz = Asg(Id "z", Binop(Sub, Deref (Id "z"),Num 1))
let bdwhi = Seq(asgny, asgnz) 
let whi = Wh(cndwhi, bdwhi)
let prt = Deref (Id "y")
let seq = Seq(whi, prt)
    
let fat = Let("x", TyInt, Num 5, 
              Let("z", TyRef TyInt, New (Id "x"), 
                  Let("y", TyRef TyInt, New (Num 1),
                      seq)))
*)

let asgny: term = Assignment (Identifier "y", BinaryOperation (Mul, Dereference (Identifier "y"), Dereference (Identifier "z")));;
let asgnz: term = Assignment (Identifier "z", BinaryOperation (Sub, Dereference (Identifier "z"), Integer 1));;
let bdwhi: term = Sequence (asgny, asgnz);;
let whi: term = While (BinaryOperation (Gt, Dereference (Identifier "z"), Integer 0), bdwhi);;
let prt: term = Dereference (Identifier "y");;
let seq: term = Sequence (whi, prt);;
let fat: term = Let ("x", Int, Integer 5, Let ("z", Reference Int, New (Identifier "x"), Let ("y", Reference Int, New (Integer 1), seq)));;

let programs: term list = [
  fatorial; fat
];;

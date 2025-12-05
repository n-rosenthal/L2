(**
  `src/Terms.ml`
  
  Definição da sintaxe de termos e de valores para a linguagem `L2`
  
*)

open Types

(** sintaxe de termos sobre `L2` *)
type term =
    | Integer of int                                (* n, termo número inteiro *)
    | Boolean of bool                               (* b, termo booleano *)
    | Identifier of string                          (* x, identificador *)
    | Conditional of term * term * term             (* If, operador condicional *)
    | BinaryOperation of binary_operator * term * term    (* bop, operação binária *)
    | While of term * term                          (* While e1 do e2 *)
    | Assignment of term * term                     (* x := e *)
    | Let of string * tipo * term * term            (* let x: T = e1 in e2 *)
    | New of term                                   (* new e *)
    | Dereference of term                           (* !e *)
    | Unit                                          (* () *)
    | Sequence of term * term                       (* e1; e2 *)
    | Location of int                               (* l, local de memória *)
and binary_operator = 
      | Add | Sub | Mul | Div                       (* operadores aritméticos *)
      | Eq  | Neq | Lt  | Leq | Gt | Geq            (* operadores relacionais *)
      | And | Or                                    (* operadores lógicos *)
;;



(** sintaxe de valores sobre `L2` *)
type value =
    | VInteger of int                               (* n, valor número inteiro *)
    | VBoolean of bool                              (* b, valor booleano *)
    | VUnit                                         (* (), unit *)
    | VLocation of int                              (* l, local de memória *)
    | EvaluationError of string                     (* s, erro de avaliação *)
and name_binding = string * value                   (* associação entre um identificador e um valor *)
;;

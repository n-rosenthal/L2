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
    | Derefence of term                             (* !e *)
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
    | VInteger of int
    | VBoolean of bool
    | VUnit
    | EvaluationError of string
and name_binding = string * value
;;

(** operadores sobre a estrutura de um termo *)

(** tamanho (size) de um termo *)
let rec size (e: term) : int = match e with
    | Integer _ -> 1
    | Boolean _ -> 1
    | Identifier _ -> 1
    | Conditional (e1, e2, e3) -> 1 + size e1 + size e2 + size e3
    | BinaryOperation (_, e1, e2) -> 1 + size e1 + size e2
    | While (e1, e2) -> 1 + size e1 + size e2
    | Assignment (e1, e2) -> 1 + size e1 + size e2
    | Let (_, _, e1, e2) -> 1 + size e1 + size e2
    | New e -> 1 + size e
    | Derefence e -> 1 + size e
    | Unit -> 1
    | Sequence (e1, e2) -> 1 + size e1 + size e2
    | Location _ -> 1
;;

(** variáveis livres de um termo *)
let rec fv (e: term) : string list = match e with
    | Integer _ -> []
    | Boolean _ -> []
    | Identifier x -> [x]
    | Conditional (e1, e2, e3) -> fv e1 @ fv e2 @ fv e3
    | BinaryOperation (_, e1, e2) -> fv e1 @ fv e2
    | While (e1, e2) -> fv e1 @ fv e2
    | Assignment (e1, e2) -> fv e1 @ fv e2
    | Let (x, _, e1, e2) -> fv e1 @ fv e2
    | New e -> fv e
    | Derefence e -> fv e
    | Unit -> []
    | Sequence (e1, e2) -> fv e1 @ fv e2
    | Location _ -> []
;;

(** coleta todos os sub-termos de um termo *)
let collect (e: term) : term list =
    let rec aux (e: term) (acc: term list) : term list = match e with
        | Integer _ -> acc
        | Boolean _ -> acc
        | Identifier _ -> acc
        | Conditional (e1, e2, e3) -> aux e1 (aux e2 (aux e3 acc))
        | BinaryOperation (_, e1, e2) -> aux e1 (aux e2 acc)
        | While (e1, e2) -> aux e1 (aux e2 acc)
        | Assignment (e1, e2) -> aux e1 (aux e2 acc)
        | Let (_, _, e1, e2) -> aux e1 (aux e2 acc)
        | New e -> aux e acc
        | Derefence e -> aux e acc
        | Unit -> acc
        | Sequence (e1, e2) -> aux e1 (aux e2 acc)
        | Location _ -> acc
    in aux e []

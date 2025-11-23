(**
  `src/Terms.ml`
  
  Definição da sintaxe de termos e de valores para a linguagem `L2`
  
*)

open Types

(** sintaxe de termos sobre `L2` *)
type term =
    | Integer of int                                (* n, termo número inteiro *)
    | Boolean of bool                               (* b, termo booleano *)
    | BinaryOperation of boperator * term * term    (* bop, operação binária *)
    | Conditional of term * term * term             (* If, operador condicional *)
    | Unit                                          (* () *)
    | Sequence of term * term                       (* e1; e2 *)
  (**
    | Identifier of string                          (* x, identificador *)
    | VarDefinition of string * tipo * term * term  (* let x: T = e1 in e2 *)
    | Assignment of string * term                   (* x := e *)
    | Derefence of term                             (* !e *)
    | Reference of term                             (* &e *)
    | While of term * term                          (* While e1 do e2 *)
  *)
and boperator = 
      | Add | Sub | Mul | Div   (* operadores aritméticos *)
      | Eq | Neq | Lt | Leq    (* operadores relacionais *)
      | And | Or               (* operadores lógicos *)
;;

(** sintaxe de valores sobre `L2` *)
type value =
    | VInteger of int
    | VBoolean of bool
    | VUnit
and name_binding = string * value
;;

let rec string_of_value v = match v with
    | VInteger n -> string_of_int n
    | VBoolean b -> string_of_bool b
    | VUnit -> "()"
;;

(** repr. string de um termo *)
let rec string_of_term t =
    match t with
    | Integer n -> string_of_int n
    | Boolean b -> string_of_bool b
    | Unit -> "()"
    | BinaryOperation (bop, t1, t2) -> "(" ^ string_of_term t1 ^ " " ^ string_of_boperator bop ^ " " ^ string_of_term t2 ^ ")"
    | Conditional (t1, t2, t3) -> "if " ^ string_of_term t1 ^ " then " ^ string_of_term t2 ^ " else " ^ string_of_term t3
    | Sequence (t1, t2) -> string_of_term t1 ^ "; " ^ string_of_term t2
and string_of_boperator bop =
    match bop with
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
    | Eq -> "=="
    | Neq -> "!="
    | Lt -> "<"
    | Leq -> "<="
    | And -> "&&"
    | Or -> "||"
and ast_of_term t = 
    match t with
    | Integer n -> "(Integer " ^ string_of_int n ^ ")"
    | Boolean b -> "(Boolean " ^ string_of_bool b ^ ")"
    | Unit -> "(Unit)"
    | BinaryOperation (bop, t1, t2) -> "(BinaryOperation (" ^ string_of_boperator bop ^ ", " ^ ast_of_term t1 ^ ", " ^ ast_of_term t2 ^ "))"
    | Conditional (t1, t2, t3) -> "(Conditional (" ^ ast_of_term t1 ^ ", " ^ ast_of_term t2 ^ ", " ^ ast_of_term t3 ^ "))"
    | Sequence (t1, t2) -> "(Sequence (" ^ ast_of_term t1 ^ ", " ^ ast_of_term t2 ^ "))"
;;


(** operadores sobre a estrutura de um termo *)

(** tamanho (size) de um termo *)
let rec size (e: term) : int = match e with
    | Integer _ -> 1
    | Boolean _ -> 1
    | BinaryOperation (_, e1, e2) -> 1 + size e1 + size e2
    | Conditional (e1, e2, e3) -> 1 + size e1 + size e2 + size e3
    | Unit -> 1
    | Sequence (e1, e2) -> 1 + size e1 + size e2
;;

(** variáveis livres de um termo *)
let rec fv (e: term) : string list = match e with
    | Integer _ -> []
    | Boolean _ -> []
    | BinaryOperation (_, e1, e2) -> fv e1 @ fv e2
    | Conditional (e1, e2, e3) -> fv e1 @ fv e2 @ fv e3
    | Unit -> []
    | Sequence (e1, e2) -> fv e1 @ fv e2
;;

(** coleta todos os sub-termos de um termo *)
let collect (e: term) : term list =
    let rec aux (e: term) (acc: term list) : term list = match e with
        | Integer n -> e :: acc
        | Boolean b -> e :: acc
        | BinaryOperation (_, e1, e2) -> aux e1 (aux e2 acc)
        | Conditional (e1, e2, e3) -> aux e1 (aux e2 (aux e3 acc))
        | Unit -> Unit :: acc
        | Sequence (e1, e2) -> aux e1 (aux e2 acc)
    in aux e [];;
;;


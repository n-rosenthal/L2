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
and binary_operator = 
      | Add | Sub | Mul | Div                       (* operadores aritméticos *)
      | Eq  | Neq | Lt  | Leq | Gt | Geq            (* operadores relacionais *)
      | And | Or                                    (* operadores lógicos *)
;;


let string_of_binary_operator (bop: binary_operator) : string =
    match bop with
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
    | Eq  -> "="
    | Neq -> "<>"
    | Lt  -> "<"
    | Leq -> "<="
    | Gt  -> ">"
    | Geq -> ">="
    | And -> "&&"
    | Or  -> "||"
;;

(** sintaxe de valores sobre `L2` *)
type value =
    | VInteger of int
    | VBoolean of bool
    | VUnit
    | Error of string
and name_binding = string * value
;;

(** repr. string de um valor *)
let rec string_of_value (v: value) : string = match v with
    | VInteger n -> string_of_int n
    | VBoolean b -> string_of_bool b
    | VUnit -> "()"
    | Error s -> "Error: " ^ s

;;

(** repr. string de um termo *)
let rec string_of_term (e: term) : string = match e with
    | Integer n -> string_of_int n
    | Boolean b -> string_of_bool b
    | Identifier x -> x
    | Conditional (e1, e2, e3) -> "if " ^ string_of_term e1 ^ " then " ^ string_of_term e2 ^ " else " ^ string_of_term e3
    | BinaryOperation (bop, e1, e2) -> string_of_term e1 ^ " " ^ string_of_binary_operator bop ^ " " ^ string_of_term e2
    | While (e1, e2) -> "while " ^ string_of_term e1 ^ " do " ^ string_of_term e2
    | Assignment (e1, e2) -> string_of_term e1 ^ " := " ^ string_of_term e2
    | Let (x, t, e1, e2) -> "let " ^ x ^ ": " ^ string_of_tipo t ^ " = " ^ string_of_term e1 ^ " in " ^ string_of_term e2
    | New e -> "new " ^ string_of_term e
    | Derefence e -> "!" ^ string_of_term e
    | Unit -> "()"
    | Sequence (e1, e2) -> string_of_term e1 ^ "; " ^ string_of_term e2
and string_of_tipo (t: tipo) : string = match t with
    | Unit -> "unit"
    | Int -> "int"
    | Bool -> "bool"
    | Reference t -> "ref " ^ string_of_tipo t
    | ErrorType s -> "Error: " ^ s
;;

(** repr. árvore de sintaxe abstrata de um termo *)
let rec ast_of_term (e: term) : string = match e with
    | Integer n -> "(Integer (Literal \"" ^ string_of_int n ^ "\"))"
    | Boolean b -> "(Boolean (Literal \"" ^ string_of_bool b ^ "\"))"
    | Identifier x -> "(Identifier \"" ^ x ^ "\")"
    | Conditional (e1, e2, e3) ->
        "(Conditional " ^
            ast_of_term e1 ^ " " ^
            ast_of_term e2 ^ " " ^
            ast_of_term e3 ^ ")"
    | BinaryOperation (bop, e1, e2) -> "(BinaryOperation (" ^ string_of_binary_operator bop ^ " " ^ ast_of_term e1 ^ " " ^ ast_of_term e2 ^ "))"
    | While (e1, e2) -> "(While (" ^ ast_of_term e1 ^ " " ^ ast_of_term e2 ^ "))"
    | Assignment (e1, e2) -> "(Assignment (" ^ ast_of_term e1 ^ " " ^ ast_of_term e2 ^ "))"
    | Let (x, t, e1, e2) -> "(Let (" ^ x ^ " " ^ string_of_tipo t ^ " " ^ ast_of_term e1 ^ " " ^ ast_of_term e2 ^ "))"
    | New e -> "(New (" ^ ast_of_term e ^ "))"
    | Derefence e -> "(Derefence (" ^ ast_of_term e ^ "))"
    | Unit -> "(Unit ())"
    | Sequence (e1, e2) -> "(Sequence (" ^ ast_of_term e1 ^ " " ^ ast_of_term e2 ^ "))"
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
    in aux e []

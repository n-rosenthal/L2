(**
    `src/Representations.ml`
    PRETTY-PRINTING para os elementos da linguagem `L2`.
    DEFINE funções que RETORNAM a REPR. em STRING de termos, valores, tipos, ambiente de tipos,
    localização na memória, memória em si, regras de inferência de tipo e de avaliação de termos.
*)

open Types
open Terms
open Constructions

let string_of_value = function
    | VInteger n        -> string_of_int n
    | VBoolean b        -> string_of_bool b
    | VUnit             -> "()"
    | VLocation l       -> "ℓ" ^ string_of_int l
    | EvaluationError s -> "[EvaluationError] " ^ s


(** repr. string de um operador binário *)
let string_of_binary_operator = function
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

(** repr. string de um tipo *)
let rec string_of_tipo : tipo -> string = function
    | Int -> "int"
    | Bool -> "bool"
    | Reference t -> "ref " ^ string_of_tipo t
    | ErrorType s -> "[TypeError] " ^ s
    | Unit -> "unit"
;;

(** retorna uma string com `2n` espaços *)
let indent (n: int) : string = String.make (2 * n) ' '   (* 2 espaços por nível *)

(** repr. string identada de um termo *)
let rec string_of_term ?(lvl=0) e =
    match e with
        | Integer n ->
            indent lvl ^ string_of_int n

        | Boolean b ->
            indent lvl ^ string_of_bool b

        | Identifier x ->
            indent lvl ^ x

        | Unit ->
            indent lvl ^ "()"

        | Conditional (e1, e2, e3) ->
            indent lvl ^ "if\n"
            ^ string_of_term ~lvl:(lvl+1) e1 ^ "\n"
            ^ indent lvl ^ "then\n"
            ^ string_of_term ~lvl:(lvl+1) e2 ^ "\n"
            ^ indent lvl ^ "else\n"
            ^ string_of_term ~lvl:(lvl+1) e3

        | While (cond, body) ->
            indent lvl ^ "while\n"
            ^ string_of_term ~lvl:(lvl+1) cond ^ "\n"
            ^ indent lvl ^ "do\n"
            ^ string_of_term ~lvl:(lvl+1) body

        | BinaryOperation (op, e1, e2) ->
            indent lvl ^ "(\n"
            ^ string_of_term ~lvl:(lvl+1) e1 ^ "\n"
            ^ indent (lvl+1) ^ string_of_binary_operator op ^ "\n"
            ^ string_of_term ~lvl:(lvl+1) e2 ^ "\n"
            ^ indent lvl ^ ")"

        | Assignment (lhs, rhs) ->
            indent lvl ^
            string_of_term lhs ^ " := " ^ string_of_term rhs

        | Let (x, t, e1, e2) ->
            indent lvl ^ "let " ^ x ^ " : " ^ string_of_tipo t ^ " =\n"
            ^ string_of_term ~lvl:(lvl+1) e1 ^ "\n"
            ^ indent lvl ^ "in\n"
            ^ string_of_term ~lvl:(lvl+1) e2

        | New e ->
            indent lvl ^ "new\n" ^ string_of_term ~lvl:(lvl+1) e

        | Dereference e ->
            indent lvl ^ "!" ^ string_of_term e

        | Sequence (e1, e2) ->
            indent lvl ^ "(\n"
            ^ string_of_term ~lvl:(lvl+1) e1 ^ ";\n"
            ^ string_of_term ~lvl:(lvl+1) e2 ^ "\n"
            ^ indent lvl ^ ")"

        | Location l ->
            indent lvl ^ "ℓ" ^ string_of_int l


(** repr. string de um termo enquanto uma árvore sintática *)
let rec ast_of_term (e: term) : string = (match e with
    | Integer n       -> "(Integer " ^ string_of_int n ^ ")"
    | Boolean b       -> "(Boolean " ^ string_of_bool b ^ ")"
    | Unit            -> "()"
    | Location l      -> "(Location " ^ string_of_int l ^ ")"
    | Identifier x    -> "(Identifier " ^ x ^ ")"
    | Conditional (a, b, c) -> "(Conditional (" ^ ast_of_term a ^ ", " ^ ast_of_term b ^ ", " ^ ast_of_term c ^ "))"
    | BinaryOperation (op, a, b) -> "(BinaryOperation (" ^ string_of_binary_operator op ^ ", " ^ ast_of_term a ^ ", " ^ ast_of_term b ^ "))"
    | While (a, b) -> "(While (" ^ ast_of_term a ^ ", " ^ ast_of_term b ^ "))"
    | Assignment (l, r) -> "(Assignment (" ^ ast_of_term l ^ ", " ^ ast_of_term r ^ "))"
    | Let (s, t, a, b) -> "(Let (" ^ s ^ ", " ^ string_of_tipo t ^ ", " ^ ast_of_term a ^ ", " ^ ast_of_term b ^ "))"
    | New a -> "(New (" ^ ast_of_term a ^ "))"
    | Dereference a -> "(Derefence (" ^ ast_of_term a ^ "))"
    | Sequence (a, b) -> "(Sequence (" ^ ast_of_term a ^ ", " ^ ast_of_term b ^ "))"
)

(** repr. string de um ambiente de tipos *)
let rec string_of_env = function
    | [] -> ""
    | (x, t) :: env ->
        "(" ^ x ^ ": " ^ string_of_tipo t ^ ") " ^ string_of_env env

(** repr. string de uma localização na memória *)
let string_of_location (loc: location) : string = "ℓ" ^ string_of_int loc


(** repr. string de uma memória *)
let rec string_of_mem = function
    | [] -> ""
    | (loc, v) :: mem ->
        "(" ^ string_of_location loc ^ ": " ^ string_of_value v ^ ") " ^ string_of_mem mem
    ;;

let string_of_rule r =
    r.name ^ " " ^ r.pre ^ " " ^ r.post
;;


(** repr. string de uma avaliação (lista de registros {nome, pré-condição, pós-condição}) *)
let rec string_of_evaluation eval =
    let rec aux = function
        | [] -> ""
        | rule :: rules ->
            "{" ^ rule.name ^ " " ^ rule.pre ^ " " ^ rule.post ^ "}\n" ^ aux rules
    in
    aux eval
;;

(** repr. string de uma inferência de tipo (lista de registros {nome, pre-condição, pós-condição}) *)
let rec string_of_type_inference type_inference =
    let rec aux = function
        | [] -> ""
        | rule :: rules ->
            "[" ^ rule.name ^ " " ^ rule.pre ^ " " ^ rule.post ^ "]\n" ^ aux rules
    in
    aux type_inference
;;
(**
    `src/Representations.ml`
    PRETTY-PRINTING para os elementos da linguagem `L2`.
    DEFINE funções que RETORNAM a REPR. em STRING de termos, valores, tipos, ambiente de tipos,
    localização na memória, memória em si, regras de inferência de tipo e de avaliação de termos.
*)

open Types
open Terms
open Constructions


(* -------------------------------------------------------------------------- *)
(* Helpers                                                                    *)
(* -------------------------------------------------------------------------- *)

let parens s = "(" ^ s ^ ")"
let braces s = "{" ^ s ^ "}"
let quote s = "\"" ^ s ^ "\""

let join sep xs =
  let rec aux = function
    | [] -> ""
    | [x] -> x
    | x :: xs -> x ^ sep ^ aux xs
  in
  aux xs

let pp_list pp xs = join " " (List.map pp xs)


(* -------------------------------------------------------------------------- *)
(* String representations for values                                          *)
(* -------------------------------------------------------------------------- *)

let string_of_value = function
  | VInteger n -> string_of_int n
  | VBoolean b -> string_of_bool b
  | VUnit      -> "()"
  | EvaluationError s -> "[RuntimeError] " ^ s


(* -------------------------------------------------------------------------- *)
(* Operators                                                                  *)
(* -------------------------------------------------------------------------- *)

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


(* -------------------------------------------------------------------------- *)
(* Types                                                                      *)
(* -------------------------------------------------------------------------- *)

let rec string_of_tipo : tipo -> string = function
  | Int -> "int"
  | Bool -> "bool"
  | Reference t -> "ref " ^ string_of_tipo t
  | ErrorType s -> "[TypeError] " ^ s
  | Unit -> "unit"
;;
(* -------------------------------------------------------------------------- *)
(* Pretty-printing for terms                                                  *)
(* -------------------------------------------------------------------------- *)

let rec string_of_term = function
  | Integer n      -> string_of_int n
  | Boolean b      -> string_of_bool b
  | Identifier x   -> x
  | Unit           -> "()"

  | Conditional (e1, e2, e3) ->
      "if " ^ string_of_term e1
      ^ " then " ^ string_of_term e2
      ^ " else " ^ string_of_term e3

  | While (cond, body) ->
      "while " ^ string_of_term cond ^ " do " ^ string_of_term body

  | BinaryOperation (op, e1, e2) ->
      parens (string_of_term e1
              ^ " " ^ string_of_binary_operator op ^ " "
              ^ string_of_term e2)

  | Assignment (lhs, rhs) ->
      string_of_term lhs ^ " := " ^ string_of_term rhs

  | Let (x, t, e1, e2) ->
      "let " ^ x ^ ": " ^ string_of_tipo t
      ^ " = " ^ string_of_term e1
      ^ " in " ^ string_of_term e2

  | New e ->
      "new " ^ string_of_term e

  | Derefence e ->
      "!" ^ string_of_term e

  | Sequence (e1, e2) ->
      string_of_term e1 ^ "; " ^ string_of_term e2

  | Location l ->
      "ℓ" ^ string_of_int l


(* -------------------------------------------------------------------------- *)
(* AST representation (sexp-like)                                             *)
(* -------------------------------------------------------------------------- *)

let constructor name parts =
  parens (name ^ " " ^ join " " parts)

let literal s =
  parens ("Literal " ^ quote s)

let rec ast_of_term = function
  | Integer n ->
      constructor "Integer" [literal (string_of_int n)]

  | Boolean b ->
      constructor "Boolean" [literal (string_of_bool b)]

  | Identifier x ->
      constructor "Identifier" [quote x]

  | Unit ->
      constructor "Unit" []

  | Conditional (e1, e2, e3) ->
      constructor "Conditional"
        [ ast_of_term e1; ast_of_term e2; ast_of_term e3 ]

  | BinaryOperation (op, e1, e2) ->
      constructor "BinaryOperation"
        [ string_of_binary_operator op;
          ast_of_term e1;
          ast_of_term e2 ]

  | While (cond, body) ->
      constructor "While" [ast_of_term cond; ast_of_term body]

  | Assignment (lhs, rhs) ->
      constructor "Assignment" [ast_of_term lhs; ast_of_term rhs]

  | Let (x, t, e1, e2) ->
      constructor "Let"
        [ quote x;
          quote (string_of_tipo t);
          ast_of_term e1;
          ast_of_term e2 ]

  | New e ->
      constructor "New" [ast_of_term e]

  | Derefence e ->
      constructor "Derefence" [ast_of_term e]

  | Sequence (e1, e2) ->
      constructor "Sequence" [ast_of_term e1; ast_of_term e2]

  | Location l ->
      constructor "Location" [string_of_int l]


(* -------------------------------------------------------------------------- *)
(* Environment printer                                                        *)
(* -------------------------------------------------------------------------- *)

let rec string_of_env = function
  | [] -> ""
  | (x, t) :: env ->
      "(" ^ x ^ ": " ^ string_of_tipo t ^ ") " ^ string_of_env env


(* -------------------------------------------------------------------------- *)
(* Type inference trace printer                                               *)
(* -------------------------------------------------------------------------- *)

let rec string_of_type_inference : type_inference -> string = function
  | [] -> ""
  | h :: rest ->
      string_of_type_rule h ^ "\n" ^ string_of_type_inference rest
and string_of_type_rule { name; requires; ensures } =
  name ^ ": " ^ requires ^ " -> " ^ ensures

(* -------------------------------------------------------------------------- *)
(* Memory printer                                                             *)
(* -------------------------------------------------------------------------- *)

let string_of_location loc = string_of_int loc

let rec string_of_mem = function
  | [] -> ""
  | (loc, s, v) :: rest ->
      "(" ^ string_of_location loc ^ ", "
          ^ s ^ ", "
          ^ string_of_value v ^ ")\n"
      ^ string_of_mem rest

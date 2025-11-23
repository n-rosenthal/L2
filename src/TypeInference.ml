(**
    `src/TypeInference.ml
    Inferência estática de tipos para a linguagem `L2`
*)

open Types
open Terms

(** exceções internas da inferência de tipos *)
exception TypeError of string * term;;
exception UnboundVariable of string;;
exception NotImplemented of string;;

let rec string_of_exn (exn: exn) : string =
    match exn with
    | TypeError (msg, t) -> "TypeError: " ^ msg ^ " em '" ^ string_of_term t ^ "'."
    | UnboundVariable x -> "UnboundVariable: " ^ x
    | NotImplemented msg -> "NotImplemented: " ^ msg
    | _ -> "Exceção desconhecida: " ^ (Printexc.to_string exn)
;;

(** ambiente de tipos *)
type env = name_binding list;;

(** lookup de um identificador no ambiente de tipos *)
let rec lookup (x: string) (env: env) : (value, exn) result =
    match env with
    | [] -> raise (UnboundVariable x)
    | (y, v) :: env -> if x = y then Ok v else lookup x env
;;

(** insere novo identificador no ambiente de tipos *)
let insert (x: string) (v: value) (env: env) : env =
    (x, v) :: env
;;

(** inferência de tipos *)
let rec typeinfer (e: term) (env: env) : (tipo, exn) result =
    match e with
    (** valores *)
    | Integer n -> Ok Int
    | Boolean b -> Ok Bool
    | Unit      -> Ok Unit

    (** if(e1, e2, e3) *)
    | Conditional (e1, e2, e3) ->
        (match typeinfer e1 env with
        | Ok Bool ->
            (match (typeinfer e2 env, typeinfer e3 env) with
            | (Ok t2, Ok t3) when t2 = t3 -> Ok t2
            | (Ok t2, Ok t3) -> Error (TypeError ("os tipos das expressões 'then' e 'else' devem ser iguais, mas foram " ^ string_of_tipo t2 ^ " e " ^ string_of_tipo t3 ^ ".", e))
            | (Error exn, _) -> Error exn
            | (_, Error exn) -> Error exn)
        | Ok t -> Error (TypeError ("o tipo da expressão 'if' deve ser booleano, mas foi " ^ string_of_tipo t ^ ".", e))
        | Error exn -> Error exn)

    (** operação binária (bop e1 e2) *)
    | BinaryOperation (bop, e1, e2) ->
        (match (typeinfer e1 env, typeinfer e2 env) with
        | (Ok t1, Ok t2) -> (match (bop, t1, t2) with
            (** op. bin. aritméticas *)
            | (Add, Int, Int) | (Sub, Int, Int) | (Mul, Int, Int) -> Ok Int

            (** op. bin. aritmética: divisão *)
            | (Div, Int, Int) -> (
                if e2 = Integer 0 then Error (TypeError ("divisão por zero", e))
                else Ok Int
            )

            (** op. bin. relacionais aritméticas *)
            | (Eq, Int, Int) | (Neq, Int, Int) | (Lt, Int, Int) | (Leq, Int, Int) -> Ok Bool

            (** op. bin. lógicas *)
            | (And, Bool, Bool) | (Or, Bool, Bool) -> Ok Bool

            | (_, t1, t2) -> Error (TypeError ("operação binária com tipos inválidos: " ^ string_of_boperator bop ^ " " ^ string_of_tipo t1 ^ " " ^ string_of_tipo t2 ^ ".", e))
            | _ -> Error (NotImplemented ("inferência de tipos para a expressão " ^ string_of_term e ^ "."))
            )
        )
    
    (* sequência, e1; e2 *)
    | Sequence (e1, e2) ->
        (match typeinfer e1 env with
        | Ok Unit -> typeinfer e2 env
        | Ok t -> Error (TypeError ("o tipo da expressão 'e1' deve ser unit, mas foi " ^ string_of_tipo t ^ " em '" ^ string_of_term e ^ "'.", e))
        | Error exn -> Error exn)
    
    | _ -> Error (NotImplemented ("inferência de tipos para a expressão " ^ string_of_term e ^ "."))
;;

let typeof (e: term) : string = 
    match typeinfer e [] with
    | Ok t -> string_of_tipo t
    | Error exn -> string_of_exn exn
;;
(**
  `src/Evaluation.ml`
  
  Avaliação de termos para a linguagem `L2`
*)


open Types
open Terms

open TypeInference

exception RuntimeError of string * term;;

(** wrapper sobre `typeinfer` para obter o tipo de um termo *)
let typeof (e: term) : string = 
    match typeinfer e [] with
    | Ok t -> string_of_tipo t
    | Error exn -> string_of_exn exn
;;

let is_value (e: term) : bool = match e with
    | Integer _ -> true
    | Boolean _ -> true
    | Unit      -> true
    | _         -> false
and is_bool (e: term) : bool = match e with
    | Boolean b -> true
    | _         -> false
and value_of_term (e: term) : value = match e with
    | Integer n -> VInteger n
    | Boolean b -> VBoolean b
    | Unit      -> VUnit
    | _ -> failwith "not a value"
and term_of_value (v: value) : term = match v with
    | VInteger n -> Integer n
    | VBoolean b -> Boolean b
    | VUnit      -> Unit
    | _ -> failwith "not a term"
;;

(** faz um passo, se possível, na avaliação de um termo *)
let rec step (e: term) (ctx: env) : term = (match e with
    (** valores *) 
    | Integer _ -> e
    | Boolean _ -> e
    | Unit      -> e

    (* if(e1, e2, e3) *)
    | Conditional (e1, e2, e3) ->
        if not (is_value e1) then (
            let e1' = step e1 ctx in
            if (e1' = e1) then raise (RuntimeError ("não foi possivel avaliar a expressão 'if'.", e))
            else step (Conditional (e1', e2, e3)) ctx
        ) else (
            let b = is_bool e1 in
            if b then step e2 ctx
            else step e3 ctx
        )

    (** operações binárias *)
    | BinaryOperation (bop, e1, e2) ->
        if not (is_value e1) then (
            let e1' = step e1 ctx in
            if (e1' = e1) then raise (RuntimeError ("não foi possivel avaliar a expressão '" ^ string_of_term e ^ "'.", e))
            else step (BinaryOperation (bop, e1', e2)) ctx
        ) else (
            if not (is_value e2) then (
                let e2' = step e2 ctx in
                if (e2' = e2) then raise (RuntimeError ("não foi possivel avaliar a expressão '" ^ string_of_term e ^ "'.", e))
                else step (BinaryOperation (bop, e1, e2')) ctx
            ) else (
                let v1 = value_of_term e1 in
                let v2 = value_of_term e2 in
                match (v1, v2, bop) with
                (* op. bin. aritméticas *)
                | (VInteger n1, VInteger n2, Add) -> Integer (n1 + n2)
                | (VInteger n1, VInteger n2, Sub) -> Integer (n1 - n2)
                | (VInteger n1, VInteger n2, Mul) -> Integer (n1 * n2)
                | (VInteger n1, VInteger n2, Div) -> (
                    if n2 = 0 then raise (RuntimeError ("divisão por zero.", e))
                    else Integer (n1 / n2)
                )

                (* op. bin. relacionais aritméticas *)
                | (VInteger n1, VInteger n2, Eq) -> Boolean (n1 = n2)
                | (VInteger n1, VInteger n2, Neq) -> Boolean (n1 <> n2)
                | (VInteger n1, VInteger n2, Lt) -> Boolean (n1 < n2)
                | (VInteger n1, VInteger n2, Leq) -> Boolean (n1 <= n2)

                (* op. bin. lógicas *)
                | (VBoolean b1, VBoolean b2, And) -> Boolean (b1 && b2)
                | (VBoolean b1, VBoolean b2, Or) -> Boolean (b1 || b2)
                | _ -> raise (RuntimeError ("tipos inválidos para a expressão '" ^ string_of_term e ^ "'.", e))
            )
        )
    
    (* sequência, e1; e2 *)
    | Sequence (e1, e2) -> (
        (** se (e1 ->* v1 & v1 : Unit) então (e1; e2 -> e2) *)

        if not (is_value e1) then (
            let e1' = step e1 ctx in
            
            (** se (e1 -/> e1') e (is_value(e1) = false) então e1 é uma forma normal inválida (erro) *)
            if (e1' = e1) then raise (RuntimeError ("forma normal invalida: '" ^ string_of_term e ^ "'.", e))
            
            (** e1 -> e1' *)
            else step (Sequence (e1', e2)) ctx
        ) else (
            (** (e1 -/> e1') e (is_value(e1) = true) => e1 = v1 *)
            let v1 = value_of_term e1 in

            (** se (v1 !: Unit) então (v1; e2 -> Erro) *)
            if not (v1 = VUnit) then raise (RuntimeError ("o tipo da expressão 'e1' deve ser unit, mas foi " ^ string_of_value v1 ^ " em '" ^ string_of_term e ^ "'.", e))
            
            (** v1; e2 -> e2 *)
            else step e2 ctx
        )
    )
    
    | _ -> raise (RuntimeError ("não foi possivel avaliar a expressão " ^ string_of_term e ^ ".", e))
) 
and stepn (e: term) (ctx: env) (n: int) : term = if n = 0 then e else stepn (step e ctx) ctx (n - 1)
and evaluate (e: term) : term = stepn e [] 1000
;;
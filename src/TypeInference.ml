(**
    `src/TypeInference.ml
    Inferência estática de tipos para a linguagem `L2`
*)

open Types
open Terms

let rec eq_tipo (t1: tipo) (t2: tipo) : bool = match t1, t2 with
    | Unit, Unit | Int, Int | Bool, Bool -> true
    | Reference t1, Reference t2 -> eq_tipo t1 t2
    | _ -> false
;;

(** ambiente de tipos: (string * tipo) list *)
type ambiente = (string * tipo) list;;


let rec string_of_env (env: ambiente) : string = match env with
    | [] -> ""
    | (x, t) :: env -> "(" ^ x ^ ": " ^ string_of_tipo t ^ ") " ^ string_of_env env
;;

(** tratamento de erros *)
let error (msg: string) (env: ambiente) : tipo = ErrorType (msg ^ "\n\t[" ^ string_of_env env ^ "]");;



(** dado um identificador `x` e um ambiente `env`,
    retorna o tipo de `x` em `env`, se `x` estiver em `env`. *)
let rec lookup (x: string) (env: ambiente) : tipo option = match env with
    | [] -> None
    | (y, t) :: env -> if x = y then Some t else lookup x env
;;


(** dado um identificador `x`, um tipo `t` e um ambiente `env`,
    adiciona/atualiza (x,t) no ambiente, preservando outras entradas. *)
let rec put (x: string) (t: tipo) (env: ambiente) : ambiente =
        match env with
        | [] -> [(x, t)]
        | (y, ty) :: env' ->
            if x = y then
              (* atualiza a primeira ocorrência *)
                (x, t) :: env'
            else
              (* preserva a cabeça e continua procurando *)
                (y, ty) :: put x t env'
;;

(** inferência estática de tipos para `L2`
    dado um termo `e` e um ambiente `env`, retorna o tipo de `e` em `env`. *)
let rec typeinfer (e: term) (env: ambiente) : tipo = (match e with 
    (** int n, número inteiro *)
    | Integer _ -> Int

    (** b, booleano *)
    | Boolean _ -> Bool

    (** x, identificador *)
    | Identifier x -> (match lookup x env with
        | Some t -> t
        | None -> ErrorType ("Identificador \"" ^ x ^ "\" não declarado sobre o ambiente\n\t[" ^ string_of_env env ^ "]")
    )

    (** if e1 then e2 else e3, operador condicional *)
    | Conditional (e1, e2, e3) -> (match typeinfer e1 env with
        | Bool -> (match typeinfer e2 env, typeinfer e3 env with
            | t2, t3 -> if t2 = t3 then t2 else ErrorType ("Os tipos de e2 e e3 em um If(e1, e2, e3) devem ser iguais, mas foram \"" ^ ast_of_term e2 ^ "\": " ^ string_of_tipo t2 ^ " e \"" ^ ast_of_term e3 ^ "\": " ^ string_of_tipo t3 ^ "\n\t" ^ string_of_env env)
            )
        | t -> ErrorType ("O tipo de e1 em um If(e1, e2, e3) deve ser Bool, mas foi \"" ^ ast_of_term e1 ^ "\": " ^ string_of_tipo t ^ "\n\t[" ^ string_of_env env ^ "]")
    )

    (** op. binárias *)
    | BinaryOperation (bop, e1, e2) -> (
        let t1, t2 = typeinfer e1 env, typeinfer e2 env in (
            match (bop, t1, t2) with
            (** op. binárias aritméticas *)
            | (Add, Int, Int) | (Sub, Int, Int) | (Mul, Int, Int) -> Int

            | (Div, Int, Int) when e2 = Integer 0 -> ErrorType ("Divisão por zero\n\t[" ^ string_of_env env ^ "]")
            | (Div, Int, Int) -> Int

            (** op. binárias aritméticas relacionais *)
            | (Eq, Int, Int) | (Neq, Int, Int) | (Lt, Int, Int) | (Leq, Int, Int)
            | (Gt, Int, Int) | (Geq, Int, Int) -> Bool

            (** op. binárias lógicas *)
            | (And, Bool, Bool) | (Or, Bool, Bool) -> Bool

            (** erro *)
            | _ -> ErrorType ("Operador binário \"" ^ string_of_binary_operator bop ^ "\" inválido sobre os tipos \"" ^ ast_of_term e1 ^ "\": " ^ string_of_tipo t1 ^ " e \"" ^ ast_of_term e2 ^ "\": " ^ string_of_tipo t2 ^ "\n\t[" ^ string_of_env env ^ "]")
        )
    )

    (** while e1 do e2 end *)
    | While (e1, e2) -> (match typeinfer e1 env with
        | Bool -> typeinfer e2 env
        | t -> ErrorType ("O tipo de e1 em um While(e1, e2) deve ser Bool, mas foi \"" ^ ast_of_term e1 ^ "\": " ^ string_of_tipo t ^ "\n\t[" ^ string_of_env env ^ "]")
    )

    (* x := e1 *)
    | Assignment (lhs, e1) -> (
        match lhs with
        | Identifier x ->
            let t_rhs = typeinfer e1 env in
            (match lookup x env with
            | Some (Reference t_ref) ->
                if t_rhs = t_ref then Unit
                else ErrorType ("Tipo incompatível em atribuição para " ^ x)
            | Some t_var ->
                ErrorType ("LHS da atribuição não é uma referência: \"" ^ x ^ "\": " ^ string_of_tipo t_var ^ "\n\t[" ^ string_of_env env ^ "]")
            | None ->
                ErrorType ("Identificador \"" ^ x ^ "\" não declarado no ambiente de tipos\n\t[" ^ string_of_env env ^ "]")
            )
        | _ ->
            ErrorType ("LHS de uma atribuição deve ser um identificador, mas foi: " ^ ast_of_term lhs ^ "\n\t[" ^ string_of_env env ^ "]")
    )

    (** let x : t = e1 in e2 *)
    | Let (x, t, e1, e2) -> (match typeinfer e1 env with
        | t' when t' = t -> typeinfer e2 (put x t env)
        | t' -> ErrorType ("O tipo de e1 em um Let(x, t, e1, e2) deve ser `t`, mas foi \"" ^ ast_of_term e1 ^ "\": " ^ string_of_tipo t' ^ "\n\t[" ^ string_of_env env ^ "]")
    )

    (** new e *)
    | New e -> (match typeinfer e env with
        | t -> Reference t
    )

    (** !e *)
    | Derefence e -> (match typeinfer e env with
        | Reference t -> t
        | t -> ErrorType ("O tipo de e em um Derefence(e) deve ser Reference(t), mas foi \"" ^ ast_of_term e ^ "\": " ^ string_of_tipo t ^ "\n\t[" ^ string_of_env env ^ "]")
    )

    (** () *)
    | Unit -> Unit

    (** e1; e2 *)
    |   Sequence (e1, e2) -> (match typeinfer e1 env with
        | Unit -> typeinfer e2 env
        | t -> ErrorType ("O tipo de e1 em um Sequence(e1, e2) deve ser Unit, mas foi \"" ^ ast_of_term e1 ^ "\": " ^ string_of_tipo t ^ "\n\t[" ^ string_of_env env ^ "]")
    )

    (** erro *)
    | _ -> ErrorType ("O algoritmo de inferência de tipos não foi capaz de inferir o tipo de \"" ^ ast_of_term e ^ "\n\t[" ^ string_of_env env ^ "]")
);;
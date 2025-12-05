(**
    `src/TypeInference.ml
    Inferência estática de tipos para a linguagem `L2`
*)

open Types              (*  tipos da linguagem `L2` *)
open Terms              (*  sintaxe de termos sobre `L2` *)
open Constructions      (*  ambiente de tipos, regras de inferência de tipo *)
open Representations    (*  repr. string para termos, valores, tipos, ambientes de tipos e memória *)

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
    | Dereference e -> (match typeinfer e env with
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

    (** location l *)
    | Location l -> (match l with
        | int -> Int
        | _ -> ErrorType ("O tipo de l em um Location(l) deve ser Int")
    )


    (** erro *)
    | _ -> ErrorType ("O algoritmo de inferência de tipos não foi capaz de inferir o tipo de \"" ^ ast_of_term e ^ "\n\t[" ^ string_of_env env ^ "]")
);;





(**
    `infer` é uma implementação de `typeinfer` que produz, além do
    tipo de um dado termo `e`, a lista de regras concretas de inferência
    `inference` para derivar o tipo de `e`.

    %XXX a escolha do nome `infer` busca somente diferenciar esta implementação
    da anterior `typeinfer`.
*)
let infer (e: term) : tipo * type_inference = (
    let rec infer' (e: term) (env: ambiente) (r: type_inference) : (tipo * ambiente * type_inference) = (match e with
        (** valores *)
        | Integer n -> (
            (Int, env, {
                name = "T-Int";
                pre = "T";
                post = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : Int";
            } :: r)
        )

        |  Boolean b -> (
            (Bool, env, {
                name = "T-Bool";
                pre = "T";
                post = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : Bool";
            } :: r)
        )

        | Identifier x -> (
            (match lookup x env with
                | Some t -> (t, env, {
                    name = "T-Var";
                    (** Γ(x) = t *)
                    pre = "Γ('" ^ x ^ "') : " ^ string_of_tipo t;

                    (** Γ ⊢ x : t *)
                    post = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t;
                    } :: r)

                | None -> (ErrorType ("UnboundIdentifier"), env, {
                    name = "T-Var Error UnboundIdentifier";
                    pre = "'" ^ x ^ "' ∉ Γ";
                    post = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo (ErrorType ("UnboundIdentifier"));
                    } :: r)
                )
            )
        
        | Conditional (e1, e2, e3) -> (
            let t1, env',   r1 = infer' e1 env r in
            let t2, env'',  r2 = infer' e2 env' r1 in
            let t3, env''', r3 = infer' e3 env'' r2 in
            (match t1, t2, t3 with
                | Bool, t2, t3 when t2 = t3 -> (t2, env''', {
                    name = "T-If";
                    pre = string_of_env env''' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Bool ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2 ^ " ∧ '" ^ ast_of_term e3 ^ "' : " ^ string_of_tipo t3;
                    post = string_of_env env''' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t2;
                    } :: r3)
                
                | Bool, t2, t3 -> (ErrorType ("O tipo das expressões e2 e e3 em um Conditional(e1, e2, e3) deve ser igual, mas foi \"" ^ ast_of_term e2 ^ "\": " ^ string_of_tipo t2 ^ " e \"" ^ ast_of_term e3 ^ "\": " ^ string_of_tipo t3 ^ "\n\t[" ^ string_of_env env ^ "]"), env''', {
                    name = "T-If Error";
                    pre = string_of_env env''' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Bool ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2 ^ " ∧ '" ^ ast_of_term e3 ^ "' : " ^ string_of_tipo t3;
                    post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("O tipo das expressões e2 e e3 em um Conditional(e1, e2, e3) deve ser igual, mas foi \"" ^ ast_of_term e2 ^ "\": " ^ string_of_tipo t2 ^ " e \"" ^ ast_of_term e3 ^ "\": " ^ string_of_tipo t3 ^ "\n\t[" ^ string_of_env env ^ "]"));
                } :: r3)

                | t1, _, _ -> (ErrorType ("O tipo de e1 em um Conditional(e1, e2, e3) deve ser Bool, mas foi \"" ^ ast_of_term e1 ^ "\": " ^ string_of_tipo t1 ^ "\n\t[" ^ string_of_env env ^ "]"), env''', {
                    name = "T-If1 Error";
                    pre = string_of_env env''' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : " ^ string_of_tipo t1;
                    post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("O tipo de e1 em um Conditional(e1, e2, e3) deve ser Bool, mas foi \"" ^ ast_of_term e1 ^ "\": " ^ string_of_tipo t1 ^ "\n\t[" ^ string_of_env env ^ "]"));
                    } :: r3)
            )
        )

        | BinaryOperation (op, e1, e2) -> (
            let t1, env',  r1 = infer' e1 env r in
            let t2, env'', r2 = infer' e2 env' r1 in
            (match op, t1, t2 with
                | Add, Int, Int 
                | Sub, Int, Int
                | Mul, Int, Int ->
                    (Int, env'', {
                        name = "T-Op" ^ string_of_binary_operator op;
                        pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Int ∧ '" ^ ast_of_term e2 ^ "' : Int";
                        post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : Int";
                        } :: r2)
                | Div, Int, Int -> (
                    if e2 = Integer 0 then (ErrorType ("Divisão por zero\n\t[" ^ string_of_env env ^ "]"),  env'', {
                        name = "T-Op" ^ string_of_binary_operator op ^ " Error";
                        pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Int ∧ '" ^ ast_of_term e2 ^ "' : Int";
                        post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("Divisão por zero\n\t[" ^ string_of_env env ^ "]"));
                        } :: r2)
                    else (Int,  env'', {
                        name = "T-Op" ^ string_of_binary_operator op ^ " Error";
                        pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Int ∧ '" ^ ast_of_term e2 ^ "' : Int";
                        post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : Int";
                        } :: r2)
                )

                | Eq, Int, Int
                | Neq, Int, Int
                | Lt, Int, Int
                | Leq, Int, Int
                | Gt, Int, Int
                | Geq, Int, Int ->
                    (Bool,  env'',  {
                        name = "T-Op" ^ string_of_binary_operator op;
                        pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Int ∧ '" ^ ast_of_term e2 ^ "' : Int";
                        post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : Bool";
                        } :: r2)

                | Eq, Bool, Bool
                | Neq, Bool, Bool ->
                    (Bool, env'',  {
                        name = "T-Op" ^ string_of_binary_operator op;
                        pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Bool ∧ '" ^ ast_of_term e2 ^ "' : Bool";
                        post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : Bool";
                        } :: r2)

                | And, Bool, Bool
                | Or, Bool, Bool ->
                    (Bool,  env'',  {
                        name = "T-Op" ^ string_of_binary_operator op;
                        pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Bool ∧ '" ^ ast_of_term e2 ^ "' : Bool";
                        post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : Bool";
                        } :: r2)

                | _ -> (ErrorType ("Operador binário inválido inválido\n\t[" ^ string_of_env env ^ "]"),  env'',  {
                    name = "T-Op" ^ string_of_binary_operator op ^ " Error";
                    pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : " ^ string_of_tipo t1 ^ " ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2;
                    post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("Operador binário inválido\n\t[" ^ string_of_env env ^ "]"));
                    } :: r2)
            )
        )

        | While (e1, e2) -> (
            let t1, env',  r1 = infer' e1 env r in
            let t2, env'', r2 = infer' e2 env' r1 in 
                (match (t1, t2) with
                    |   Bool, Unit -> (Unit,  env'', {
                            name = "T-While";
                            pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Bool ∧ '" ^ ast_of_term e2 ^ "' : Unit";
                            post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : Unit";
                            } :: r2)
                    
                    |   _ -> (ErrorType ("While inválido\n\t[" ^ string_of_env env ^ "]"),  env'', {
                            name = "T-While Error";
                            pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : " ^ string_of_tipo t1 ^ " ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2;
                            post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("While inválido\n\t[" ^ string_of_env env ^ "]"));
                            } :: r2)
                )
        )

        | Assignment (e1, e2) ->(
            let t1, env', r1 = infer' e1 env r in
            let t2, env'', r2 = infer' e2 env' r1 in
                (match (t1, t2) with
                    |   Reference t1, t2 when t1 = t2 -> (Unit,  env'', {
                            name = "T-Atr";
                            pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : " ^ string_of_tipo t1 ^ " ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2;
                            post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : Unit";
                            } :: r2)
                    |   _ -> (ErrorType ("Atribuição inválida\n\t[" ^ string_of_env env ^ "]"),  env'', {
                            name = "T-Atr Error";
                            pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : " ^ string_of_tipo t1 ^ " ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2;
                            post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("Atribuição inválida\n\t[" ^ string_of_env env ^ "]"));
                            } :: r2)
                )
        )

        | Let (x, t, e1, e2) -> (
            let t1, env', r1 = infer' e1 env r in
            let t2, env'', r2 = infer' e2 (put x t env') r1 in
                (match (t1, t2) with
                    |   t1, t2 when t1 = t2 -> (t2,  env'', {
                            name = "T-Let";
                            pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : " ^ string_of_tipo t1 ^ " ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2;
                            post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t2;
                            } :: r2)
                    |   t1, t2 -> (ErrorType ("Let inválido com x=" ^ x ^ " t1=" ^ string_of_tipo t1 ^ " t2=" ^ string_of_tipo t2 ^ "\n\t[" ^ string_of_env env ^ "]"),  env'', {
                            name = "T-Let Error";
                            pre  = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : " ^ string_of_tipo t1 ^ " ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2;
                            post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("Let invável\n\t[" ^ string_of_env env ^ "]"));
                            } :: r2)
                )
        )

        | New e -> (
            let t, env', r' = infer' e env r in
            (Reference t,  env', {
                name = "T-New";
                pre = string_of_env env' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t;
                post = string_of_env env' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo (Reference t);
                } :: r')
        )

        | Dereference e -> (
            let t, env', r' = infer' e env r in
            (match t with
                | t -> (t, env', {
                    name = "T-Deref";
                    pre = string_of_env env' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t;
                    post = string_of_env env' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t;
                    } :: r')
                | _ -> (ErrorType ("Dereferência inválida\n\t[" ^ string_of_env env ^ "]"), env', {
                    name = "T-Deref Error";
                    pre = string_of_env env' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t;
                    post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("Dereferência inválida\n\t[" ^ string_of_env env ^ "]"));
                    } :: r')
            )
        )

        | Unit -> (Unit, env, {
            name = "T-Unit";
            pre = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : Unit";
            post = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : Unit";
            } :: r)

        | Sequence (e1, e2) -> (
            let t1, env', r1 = infer' e1 env r in
            let t2, env'', r2 = infer' e2 env' r1 in
                (match (t1, t2) with
                    |   Unit, t2 -> (t2, env'', {
                            name = "T-Sequence";
                            pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Unit ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2;
                            post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t2;
                            } :: r2)
                    |   _ -> (ErrorType ("Sequence invável\n\t[" ^ string_of_env env ^ "]"), env'', {
                            name = "T-Sequence Error";
                            pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : " ^ string_of_tipo t1 ^ " ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2;
                            post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("Sequence invável\n\t[" ^ string_of_env env ^ "]"));
                            } :: r2)
                )
        )

        | Location l -> (
            let t, env', r' = infer' e env r in
            (match t with
                | Reference t -> (t, env', {
                    name = "T-Location";
                    pre = string_of_env env' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t;
                    post = string_of_env env' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t;
                    } :: r')
                | _ -> (ErrorType ("Location inválida\n\t[" ^ string_of_env env ^ "]"), env', {
                    name = "T-Location Error";
                    pre = string_of_env env' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t;
                    post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("Location inválida\n\t[" ^ string_of_env env ^ "]"));
                    } :: r')
            )
        )

        | _ -> (ErrorType ("Expressão inválida\n\t[" ^ string_of_env env ^ "]"), env, {
            name = "T-Error";
            pre = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo (ErrorType ("Expressão inválida\n\t[" ^ string_of_env env ^ "]"));
            post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("Expressão inválida\n\t[" ^ string_of_env env ^ "]"));
            } :: r)
    ) in
    let t, env', r = infer' e [] [] in
    (t, List.rev r)
);;

(**
    Wrapper sobre `infer e` que permite obter o tipo de um termo `e`
    e ignorar as regras de inferência de tipo usadas para tipá-lo. *)
let typeof (e: term) : tipo = fst (infer e);;
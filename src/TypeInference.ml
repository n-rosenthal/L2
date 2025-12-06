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

    (* e1 := e2 
       x : ref t, e1 : t => x := e1 : unit *)
    | Assignment (e1, e2) -> (
        let t1, t2 = typeinfer e1 env, typeinfer e2 env in
        match t1 with
        | Reference t when t = t2 -> Unit
        | _ -> ErrorType ("O tipo de e1 em um Assignment(e1, e2) deve ser Reference(t), mas foi \"" ^ ast_of_term e1 ^ "\": " ^ string_of_tipo t1 ^ "\n\t[" ^ string_of_env env ^ "]")
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
        | t -> ErrorType ("O tipo de e em um Dereference(e) deve ser Reference(t), mas foi \"" ^ ast_of_term e ^ "\": " ^ string_of_tipo t ^ "\n\t[" ^ string_of_env env ^ "]")
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

        (** Identifier x, variáveis
            O tipo de um identificador `x` é o tipo associado a ele no ambiente de tipos `env`. 

                Γ(x) = t => Γ ⊢ x : t
            
            Se `x` não estiver no ambiente de tipos `env`, então `Identifier x` : TypeError
            é gerado um erro de variável não declarada.
        *)
        | Identifier x -> (
            (match lookup x env with
                | Some t -> (t, env, {
                    name = "T-Var";
                    (** Γ(x) = t *)
                    pre = "Γ('" ^ x ^ "') : " ^ string_of_tipo t;

                    (** Γ ⊢ x : t *)
                    post = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t;
                    } :: r)

                | None -> (ErrorType ("Identificador " ^ x ^ " não declarado sobre o ambiente " ^ string_of_env env), env, {
                    name = "T-Var Error Variável não declarada";
                    pre = "'" ^ x ^ "' ∉ Γ";
                    post = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo (ErrorType ("UnboundIdentifier"));
                    } :: r)
                )
            )
        

        (** if e1 then e2 else e3, operador condicional
            O tipo de um operador condicional `if e1 then e2 else e3` será o tipo de um de seus branches (e2 ou e3).
            Em L_2, é necessário que os tipos do then (`e2`) e do else (`e3`) sejam iguais, então

                se `e1` : Bool, e `e2` e `e3` : t, então Γ ⊢ if e1 then e2 else e3 : t
            
            Se `e1` não for uma expressão booleana, então um erro é levantado;
            Se os tipos de `e2` e `e3` não forem iguais, então um erro é levantado.
        *)
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

        (** operações binárias (BinaryOperation (bop, e1, e2)) 
            O tipo de uma operação binária `e1 bop e2` depende do operador `bop` e dos tipos de `e1` e `e2`.
            Para as operações binárias artiméticas
                bop =   Add, Sub, Mul, Div
                e1  :   Int
                e2  :   Int
                
                =>  (bop e1 e2) : Int
            
            para as operações binárias aritméticas relacionais
                bop =   Eq, Neq, Gt, Geq, Lt, Leq
                e1  :   Int
                e2  :   Int
                
                =>  (bop e1 e2) : Bool
                
            para as operações binárias lógicas relacionais
                bop =   Eq, Neq
                e1  :   Bool
                e2  :   Bool
                
                =>  (bop e1 e2) : Bool
            
            e para as operações binárias lógicas somente
                bop =   And, Or
                e1  :   Bool
                e2  :   Bool
                
                =>  (bop e1 e2) : Bool
        
            quaisquer outras configurações, que não estas, geram erro de tipo `ErrorType`.
            *)
        | BinaryOperation (op, e1, e2) -> (
            let t1, env',  r1 = infer' e1 env r in
            let t2, env'', r2 = infer' e2 env' r1 in
            (match op, t1, t2 with
                (** op. binárias aritméticas (bop, Int, Int) : Int *)
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

                (** op. binárias aritméticas relacionais (bop, Int, Int) : Bool *)
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

                (** op. binárias lógicas relacionais (bop, Bool, Bool) : Bool *)
                | Eq, Bool, Bool
                | Neq, Bool, Bool ->
                    (Bool, env'',  {
                        name = "T-Op" ^ string_of_binary_operator op;
                        pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Bool ∧ '" ^ ast_of_term e2 ^ "' : Bool";
                        post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : Bool";
                        } :: r2)

                (** op. binárias lógicas (bop, Bool, Bool) : Bool *)
                | And, Bool, Bool
                | Or, Bool, Bool ->
                    (Bool,  env'',  {
                        name = "T-Op" ^ string_of_binary_operator op;
                        pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Bool ∧ '" ^ ast_of_term e2 ^ "' : Bool";
                        post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : Bool";
                        } :: r2)

                (** erro *)
                | _ -> (ErrorType ("Operador binário inválido inválido\n\t[" ^ string_of_env env ^ "]"),  env'',  {
                    name = "T-Op" ^ string_of_binary_operator op ^ " Error";
                    pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : " ^ string_of_tipo t1 ^ " ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2;
                    post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("Operador binário inválido\n\t[" ^ string_of_env env ^ "]"));
                    } :: r2)
            )
        )

        (** while e1 do e2 end 
            e1 : Bool ∧ e2 : Unit => while e1 do e2 : Unit
            
            `e1` é a condição do while. enquanto `e1` for verdadeiro, o corpo `e2` é executado. 
            `e1` portanto deve ser uma expressão booleana.
            
            `e2` é o corpo do while e deve ser um comando imperativo que é avaliado para `Unit`. 
            
            `while e1 do e2 end` é avaliado para `Unit`. *)
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


        (** e1 := e2
            `e1`    deve ser um ponteiro para uma posição na memória.
                    deve ser uma referência (Identifier `x`)
                    portanto `e1` deve ser tipado `Reference t`
                    isto é, uma referência ao tipo `t`, que é o tipo do objeto na memória.

                    se um Identifier `x` aponta para um inteiro `VInteger 5` na posição `2` na memória
                    então Identifier `x` : Reference Int
            
            `e2`    deve ser um termo que seja avaliado para um `t`.

            `e1 := e2` é um comando imperativo que é avaliado para Unit; seu tipo é Unit.

            `e1` : ref t ∧ `e2` : t => `e1` := `e2` : Unit
            *)
        | Assignment (e1, e2) ->(
            let t1, env', r1 = infer' e1 env r in
            let t2, env'', r2 = infer' e2 env' r1 in
                (match (t1, t2) with
                    |   Reference t1, t2 when t1 = t2 -> (Unit,  env'', {
                            name = "T-Atr";
                            pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : " ^ string_of_tipo t1 ^ " ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2;
                            post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : Unit";
                            } :: r2)
                    |   _ -> (ErrorType ("Atribuição inválida. teve os tipos t1=" ^ string_of_tipo t1 ^ " e t2=" ^ string_of_tipo t2
                                        ^ " e1=" ^ ast_of_term e1 ^ " e2=" ^ ast_of_term e2),  env'', {
                            name = "T-Atr Error";
                            pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : " ^ string_of_tipo t1 ^ " ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2;
                            post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("Atribuição inválida\n\t[" ^ string_of_env env ^ "]"));
                            } :: r2)
                )
        )

        (**
            let x : t = e1 in e2
            
            `x` é o nome de um identificador (Identifier `x`)
            `t` é o tipo desta variável, e que deve ser idêntico ao tipo de `e1`
            `e1` é uma expressão cujo valor queremos associar ao `Identifier x`
            `e2` é onde queremos usar o identificador, isto é, iremos substituir toda
                    ocorrência de `Identifier x` pelo valor de `e1` em `e2`
                    
            então
            
            `e1` : t ∧ `e2` : t' => `let x = e1 in e2*)
        | Let (x, t, e1, e2) -> (
            let t1, env', r1 = infer' e1 env r in
            let env'' = (x, t) :: env' in
            let t2, env''', r2 = infer' e2 env'' r1 in
                (t2, env''', {
                    name = "T-Let";
                    pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : " ^ string_of_tipo t1 ^ " ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2;
                    post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t2;
                    } :: r2)
        )

        (**
            new e
            
            `e` : t => `new e` : Reference(t)
            
            A expressão `new e` busca criar uma nova referência ao termo `e`
            Quando usado em uma atribuição
                `e1 := new e`
            
            `e1` será um ponteiro para uma referência ao termo `e`
        *)
        | New e -> (
            let t, env', r' = infer' e env r in
            (Reference t,  env', {
                name = "T-New";
                pre = string_of_env env' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t;
                post = string_of_env env' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo (Reference t);
                } :: r')
        )

        (**
            `!e`
            
            `e` : Reference(t) => `!e` : t

            Se `e` for um ponteiro para um termo de tipo `t`
            então `!e` será um termo de tipo `t`. (pois `!e` é o valor que `e` aponta etc)
        *)
        | Dereference e -> (
            let t, env', r' = infer' e env r in
            (match t with
                | Reference t -> (t, env', {
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


        (** Termo Unit é de tipo Unit. *)
        | Unit -> (Unit, env, {
            name = "T-Unit";
            pre = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : Unit";
            post = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : Unit";
            } :: r)

        (**
            `e1; e2
            Sequência de expressões
            
            `e1` deve ser um comando imperativo que seja avaliado para Unit.
            `e2` deve ser um termo de tipo `t`, então
            
            `e1; e2 : t`, pois `e1; e2 -> Unit, e2 -> e2` na avaliação. *)
        | Sequence (e1, e2) -> (
            let t1, env', r1 = infer' e1 env r in
            let t2, env'', r2 = infer' e2 env' r1 in
                (match (t1, t2) with
                    |   Unit, t -> (t,  env'', {
                            name = "T-Sequence";
                            pre = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Unit ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t;
                            post = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e ^ "' : " ^ string_of_tipo t;
                            } :: r2)
                    |   t, t' -> (ErrorType ("Uma sequência `e1; e2` deve ter `e1` tipado como Unit, mas teve " ^ string_of_tipo t),  env'', {
                            name = "T-Sequence Error";
                            pre  = string_of_env env'' ^ " ⊢ '" ^ ast_of_term e1 ^ "' : Unit ∧ '" ^ ast_of_term e2 ^ "' : " ^ string_of_tipo t2;
                            post = ast_of_term e ^ " : " ^ string_of_tipo (ErrorType ("Sequence inválida\n\t[" ^ string_of_env env ^ "]"));
                            } :: r2)
                )
        )

        
        (** Localização l na memória
            Se `l` for um local na memória, então `l` : Reference(t)
            
            `l` : Reference(t)
        *)
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
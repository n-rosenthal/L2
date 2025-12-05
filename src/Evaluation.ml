(**
    `src/Evaluation.ml`
    DEFINE as funções de AVALIAÇÃO de termos para linguagem L2.

    Avaliação de termos para a linguagem `L2`.
*)


open Types                  (*  tipos da linguagem `L2` *)
open Terms                  (*  sintaxe de termos sobre `L2` *)
open Constructions          (*  memória de valores, regras de avaliação de termos *)
open Representations        (*  repr. string para termos, valores, tipos, ambientes de tipos e memória *)
open TypeInference          (*  inferência estática de tipos para `L2` *)


(** ---
    Predicados para avaliação small-step e conversão entre formas
    --- 
*)

(** verifica se um termo representa um valor *)
let is_value_term = function
    | Integer _ | Boolean _ | Unit | Location _ -> true
    | _ -> false

(** converte um termo para um valor *)
let value_of_term = function
    | Integer n -> Some (VInteger n)
    | Boolean b -> Some (VBoolean b)
    | Unit      -> Some VUnit
    | Location l ->
        (* location is a value but its runtime value is found in memory *)
        None
    | _ -> None

(** converte um valor para um termo *)
let term_of_value = function
    | VInteger n -> Some (Integer n)
    | VBoolean b -> Some (Boolean b)
    | VUnit      -> Some Unit
    | _ -> None

(** ---
    aplicação de operações bináras sobre valores
    ---
*)

(** dados dois valores `v` e `u`, e uma operador binário `bop`,
    tenta aplicar `(bop v u)` e retornar seu resultado;
    se não for possível, um termo `RuntimeError s` será retornado *)
let apply_binop bop v1 v2 =
        match (bop, v1, v2) with
        | (Add, VInteger a, VInteger b) -> VInteger (a + b)
        | (Sub, VInteger a, VInteger b) -> VInteger (a - b)
        | (Mul, VInteger a, VInteger b) -> VInteger (a * b)
        | (Div, VInteger _, VInteger 0) -> EvaluationError "Divisão por zero"
        | (Div, VInteger a, VInteger b) -> VInteger (a / b)

        | (Eq, VInteger a, VInteger b)  -> VBoolean (a = b)
        | (Neq, VInteger a, VInteger b) -> VBoolean (a <> b)
        | (Lt, VInteger a, VInteger b)  -> VBoolean (a < b)
        | (Leq, VInteger a, VInteger b) -> VBoolean (a <= b)
        | (Gt, VInteger a, VInteger b)  -> VBoolean (a > b)
        | (Geq, VInteger a, VInteger b) -> VBoolean (a >= b)

        | (Eq, VBoolean a, VBoolean b)  -> VBoolean (a = b)
        | (Neq, VBoolean a, VBoolean b) -> VBoolean (a <> b)

        | (And, VBoolean a, VBoolean b) -> VBoolean (a && b)
        | (Or,  VBoolean a, VBoolean b) -> VBoolean (a || b)

        | _ -> EvaluationError ("Erro de tipo para o operador binário " ^ (string_of_binary_operator bop) ^
                                " sobre os termos " ^ (string_of_value v1) ^ " e " ^ (string_of_value v2))
;;

(** substitui toda ocorrência de um termo `x` por um valor `v`
    em um termo `e`.

    uso: substitute (Identifier "x") v e
*)
let rec substitute (x : term) (v : value) (e : term) : term =
    match e with
    (** caso-base: é exatamente (Identifier x) *)
    | Identifier x -> if x = x then (Option.get (term_of_value v)) else e

    (** valores  *)
    | Integer n -> Integer n
    | Boolean b -> Boolean b
    | Unit -> Unit

    | BinaryOperation (op, e1, e2) ->
        BinaryOperation (op, substitute x v e1, substitute x v e2)

    | Conditional (e1, e2, e3) ->
        Conditional (
            substitute x v e1,
            substitute x v e2,
            substitute x v e3
        )

    | Let (id, t, e1, e2) ->
        (** regra usual da substituição:
            - substitui em e1 SEM restrições
            - substitui em e2 **somente se** o id do Let não é o x
        *)
        (match x with
            | Identifier xname ->
                if id = xname then
                (** sombra: x foi redefinido neste let, não substituímos em e2 *)
                Let (id, t,
                        substitute x v e1,
                        e2)
                else
                Let (id, t,
                        substitute x v e1,
                        substitute x v e2)
        | _ ->
            Let (id, t,
                substitute x v e1,
                substitute x v e2)
        )

    | Sequence (e1, e2) ->
        Sequence (substitute x v e1, substitute x v e2)

    | While (cond, body) ->
        While (substitute x v cond, substitute x v body)

    | Assignment (e1, e2) ->
        Assignment (substitute x v e1, substitute x v e2)

    | Dereference e1 -> (match e1 with
        | Identifier x -> Identifier x
        | _ -> Dereference (substitute x v e1)
    )

    | New e1 ->
        New (substitute x v e1)


(** tipo resultado de passo de avaliação
    O resultado de um passo de avaliação sobre um termo `e` pode ser
        OU  um termo `e'`
        OU  um valor `v`
*)
type step_result =
    | Term of term
    | Value of value
;;





(** ---
    Avaliação de termos
    ---
*)

(** faz um passo na avaliação de um termo, se for possível
    um passo, na avaliação de um termo `e`,
        sobre uma tabela de símbolos `table`, e
        sobre uma memória `mem`
    
    retorna um passo de avaliação `step_result`
        que pode ser ou um termo `e'` ou um valor `v`
    além da tabela de símbolos e da memória, possivelmente atualizadas,
    e da regra de avaliação usada para provar `e -> e'`
*)
let rec step    (e     :     term)
                (table :  symbols)
                (mem   :   memory)
                :   step_result * symbols * memory * rule =
    match e with 
        (** termos que são valores são imediatamente avaliados para seus respectivos valores *)
        Integer n -> (Value (VInteger n), table, mem, {
            name    = "E-Int";
            pre     = "T";
            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value (VInteger n) ^ ", " ^ string_of_mem mem;
        })

        | Boolean b -> (Value (VBoolean b), table, mem, {
            name    = "E-Bool";
            pre     = "T";
            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value (VBoolean b) ^ ", " ^ string_of_mem mem;
        })

        | Unit      -> (Value VUnit, table, mem, {
            name    = "E-Unit";
            pre     = "T";
            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value VUnit ^ ", " ^ string_of_mem mem;
        })
        
        | Location l -> (Value (VLocation l), table, mem, {
            name    = "E-Location";
            pre     = "T";
            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value (VLocation l) ^ ", " ^ string_of_mem mem;
        })

        (**
            Dereferência
            Dereference e

            !e : recupera o valor que está na posição de memória que `e` aponta 
            
            `e` deve ser avaliado para (VLocation l)

            1.  se `e` não for um valor, então avalie-o até que seja.
            2.  se `e` = `v` for um valor, então
                2.1.  verifique se `v` é uma VLocation l
                    2.1.2  se `v` = VLocation l, então
                        2.1.2.1  tente extrair o valor da memória para a posição `l`
                        2.1.2.2  se falhar, então produza um erro
                        2.1.2.3  senão, retorne o valor
                    2.1.3  senão, produza um erro
                2.2.  senão, produza um erro
            3.  senão, produza um erro etc
        *)      
        | Dereference e -> (match e with
                | Identifier x -> (match search x table with
                    (** tenta obter a posição de `x` na tabela de símbolos *)
                    |   Some l -> (match get l mem with
                        | Some v -> (match term_of_value v with
                            | Some vv -> (Term vv, table, mem, {
                                name    = "E-Deref";
                                pre     = "";
                                post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value v ^ ", " ^ string_of_mem mem;
                            })

                            | None -> Value (EvaluationError ("e=" ^ ast_of_term e ^ ", l=" ^ string_of_int l ^ ", mem=" ^ string_of_mem mem)),
                                table, mem, {
                                name = "E-Deref Error 1";
                                pre  = "";
                                post = "";
                            })
                    )

                    | None -> Value (EvaluationError ("Identificador nao declarado: `" ^ x ^ "`")),
                        table, mem, {
                        name = "E-Deref Error 2";
                        pre  = "";
                        post = "";
                    })

                | Location l | Integer l -> (
                    match get l mem with
                        | Some v -> (Value v, table, mem, {
                            name    = "E-Deref";
                            pre     = "";
                            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value v ^ ", " ^ string_of_mem mem;
                        })

                        | None -> Value (EvaluationError ("e=" ^ ast_of_term e ^ ", l=" ^ string_of_int l ^ ", mem=" ^ string_of_mem mem)),
                            table, mem, {
                            name = "E-Deref Error 2";
                            pre  = "";
                            post = "";
                        }
                )

            | _ -> Value (EvaluationError ("e=" ^ ast_of_term e ^ ", mem=" ^ string_of_mem mem)),
                table, mem, {
                name = "E-Deref Error 3";
                pre  = "";
                post = "";
            }
        )

        (**
            Let x : t = e1 in e2
            
            Define o identificador `x`, de tipo `t`.
            Verifica se `e1` é tipado `t`. Se não for, erro;
            
            Se `e1` não for um valor, avalia `e1` até que seja.
            Quando `e1` for um valor,
                (1)
                    [Tome a string `x` e monte um identificador `Identifier x`]
                    Associe o identificador `x` à tabela de símbolos.
                    Extraia a posição da memória `l` associada à `x`, na tabela de símbolos.
                
                (2)
                    Crie uma nova posição na memória em `l` e associe essa nova posição ao valor `e1`,
                    dessa forma armazenamos     `x` na tabela de símbolos
                                        e        `e1` = `v` na memória em mem[l]
            
                (3)
                    Substitua toda ocorrência de (Identifier x) em `e2` por `v`.
            
                (4)
                    retorne `e2`, ..., etc.
        *)
        | Let (x, t, e1, e2) -> (
            (** verifica se `e1` é tipado em `t` *)
            let (t1, _) = infer e1 in
            if t1 = t then
                (** e1 : t, então verifique se e1 é um valor *)
                if not (is_value_term e1) then 
                    (match step e1 table mem with
                        | Term e1', _, _, _ -> step (Let (x, t, e1', e2)) table mem
                        | Value v1, _, _, _ -> Value (EvaluationError "Erro ao avaliar um termo"), table, mem, {
                            name    = "E-Let Error 1";
                            pre     = "";
                            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value v1 ^ ", " ^ string_of_mem mem;
                        })
                
                (** `e1 = v1` é um valor, então ... *)
                else(
                    (*  1.  Associe o identificador `x` à tabela de símbolos. *)
                    (*  Verifique se o identificador `x` já não está na tabela de símbolos *)
                    if is_bound x table then
                        Value (EvaluationError ("Identificador duplicado: `" ^ x ^ "`")), table, mem, {
                            name    = "E-Let Error 2";
                            pre     = "";
                            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value (EvaluationError ("Identificador duplicado: `" ^ x ^ "`")) ^ ", " ^ string_of_mem mem;
                        }
                    else
                        (*  Extraia a próxima posição disponível na memória *)
                        let l = where mem in

                        (*  Associe o identificador `x` à posição `l`, na tabela de símbolos *)
                        let table' = extend x l table in

                        (*  extraia o valor de e1 *)
                        match value_of_term e1 with
                        | Some v1 -> (
                            (*  Crie uma nova posição na memória em `l` e associe essa nova posição ao valor `e1`,
                                dessa forma armazenamos         `x` na tabela de símbolos
                                                    e           `e1` = `v` na memória em mem[l] *)
                            let l = where mem in
                            let mem' = set l v1 mem in

                            (*  Substitua toda ocorrência de (Identifier x) em `e2` por `v`. *)
                            (* let e2' = substitute (Identifier x) v1 e2 in *)

                            (*  retorne `e2`, ..., etc. *)
                            Term e2, table', mem', {
                                name    = "E-Let";
                                pre     = "";
                                post    = "e2=" ^ ast_of_term e2;
                            }
                        )

                        | None -> Value (EvaluationError ("`e1` deveria derivar para um valor `v1` mas é " ^ string_of_term e1)), table, mem, {
                            name    = "E-Let Error 1";
                            pre     = "";
                            post    = "";
                        }
                )
                    else
                        Value (EvaluationError ("`e1` deveria derivar para um valor `v1` mas é " ^ string_of_term e1)), table, mem, {
                            name    = "E-Let Error 1";
                            pre     = "";
                            post    = "";
                    })

        (**
            Atribuição
            Assignment e1 e2 
            e1 := e2

            e1 deve avaliar para uma variável (Identifier x)
            e2 deve avaliar para um valor
            
        Ordem de avaliação da esquerda para a direita
        Se `e1` não for um valor, então avalie-o até que seja;
        Se `e1` = `v1` for um valor, então decide se
            `v1` é um identificador (variável, `Identifier x`):
                Se `e2` não for um valor, então avalie-o até que seja;
                Se `e2` = `v2` for um valor, então atualize `mem[x]` com `v2` e retorne Unit;
            `v1` é um local de memória (`Location l`):
                Se `e2` não for um valor, então avalie-o até que seja;
        Assignment: step left, right; when lhs identifies a location update memory and become Unit *)
        | Assignment (e1, e2) ->
            (match e1 with
                (** `e1` = `x` Identifier x *)
                | Identifier x -> (
                    (** verificar se `x` é um identificador (variável) na tabela de símbolos *)
                    if not (is_bound x table) then (
                        (Value (EvaluationError ("Identificador nao declarado: `" ^ x ^ "`")), table, mem, {
                            name    = "E-Atr Error 1";
                            pre     = "";
                            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value (EvaluationError ("Identificador nao declarado: `" ^ x ^ "`")) ^ ", " ^ string_of_mem mem;
                    }))
                    (* se `e2` não for um valor, então avalie-o até que seja *)
                    else(                
                        if not (is_value_term e2) then (match step e2 table mem with
                            | Term e2', _, _, _ -> step (Assignment (Identifier x, e2')) table mem
                            | Value v, _, _, _ -> Value (EvaluationError "Erro ao avaliar um termo"), table, mem, {
                                name    = "E-Atr Error 2";
                                pre     = "";
                                post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value v ^ ", " ^ string_of_mem mem;
                            }
                        )
                        else (
                            (* `e2` = `v2` é um valor, então tente descobrir a posição na memória ocupada pelo Identificador x  *)
                            (match search x table with
                                (** `v2` é um identificador (variável) que não existe na memória, erro. *)
                                | None -> Value (EvaluationError ("Atribuição: identificador '" ^ x ^ "' nao encontrado na memória " ^ string_of_mem  mem)), table, mem, {
                                    name    = "E-Atr 1";
                                    pre     = "v2 nao tinha um domínio na memória " ^ string_of_mem mem;
                                    post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value (EvaluationError "Erro ao extrair um valor da memória") ^ ", " ^ string_of_mem mem;
                                }

                                (** `v2` é um identificador (variável) que existe na memória, e sua posição é `loc` *)
                                | Some loc ->
                                    (** extraia o valor de `e2` *)
                                    (match value_of_term e2 with
                                    | Some vv ->
                                        (** atualize `mem[x]` com `v2` e retorne Unit *)
                                        let mem' = set loc vv mem in
                                        (Term Unit, table, mem', {
                                            name    = "E-Atr 1";
                                            pre     = "(Location " ^ string_of_int loc ^ ") está no domínio da memória " ^ string_of_mem mem;
                                            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (Assignment (e1, e2)) ^ ", " ^ string_of_mem mem';
                                        })
                                    | None ->
                                        (Value (EvaluationError ("Atribuição: nao foi possivel avaliar " ^ ast_of_term e2)), table, mem, {
                                            name    = "E-Atr 1";
                                            pre     = "(Location " ^ string_of_int loc ^ ") está no domínio da memória " ^ string_of_mem mem;
                                            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (Assignment (e1, e2)) ^ ", " ^ string_of_mem mem;
                                    })))
                        ))
                    )

                | _ -> 
                    (Value (EvaluationError ("Atribuição: nao foi possivel avaliar " ^ ast_of_term e1)), table, mem, {
                        name    = "E-Atr 1";
                        pre     = "";
                        post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (Assignment (e1, e2)) ^ ", " ^ string_of_mem mem;
                }))
                

        (**
            Identificadores ou variáveis
            Identifier x

            Um identificador `x` representa uma variável do programa.
            O programador tem acesso somente a variáveis (identificadores),
            não tendo acesso a posições na memória. Isto é feito a partir do
            avaliador/compilador.

            É necessário então procurar na tabela de símbolos pelo identificador `x`.
            Se `x` estiver na tabela, então acesse a localização na memória ( a tabela
            é uma lista de pares identificador * posição na memória ).

            Aqui, a avaliação de um identificador `x` produz uma localização na memória

                (Identifier x) -> (Location l) -> (VLocation v)
            
            1.  verifique se `x` está na tabela de símbolos;
                1.1.    se estiver, recupere a localização apontada por `x` na memória
                1.2.    senão, produza um erro.
            2.  avalie para a localização na memória.
            *)
        | Identifier x -> (
            (* verifica a tabela de símbolos para verificar se `x` está lá *)
            if is_bound x table then
                (** extrai o local da memória, correspondente ao `x` na tabela de símbolos `table` *)
                match search x table with 
                    | Some l -> (
                        Term (Location l), table, mem, {
                            name    = "E-Id";
                            pre     = "";
                            post    = x ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value (VLocation l) ^ ", " ^ string_of_mem mem;
                        }
                    )

                    | None -> Value (EvaluationError ("Identificador não declarado: `" ^ x ^ "`")),
                        table, mem,
                        {name = "E-Id Error";
                        pre  = "";
                        post = "";
                        }
            else Value (EvaluationError ("Identificador não declarado: `" ^ x ^ "`")),
                table, mem, {
                    name = "E-Id Error";
                    pre  = "";
                    post = "";
                }
        )

        

        
        (** new e 
            se `e` não for um valor, avalie-o até que seja;
            se `e` for um valor,
                defina um novo local na memória
                associe o valor de `e` ao local na memória
            a avaliação de `new e` produz o local da memória `l` *)
        | New e -> (
            (** se `e` não for um valor, avalie-o até que seja um termo *)
            if not (is_value_term e) then (match step e table mem with
                | Term e', _, _, _ -> step (New e') table mem
                
                (** erro, isto não pode acontecer *)
                | Value v, _, _, _ -> (
                    Value (EvaluationError "Erro ao avaliar um termo"), table, mem, {
                        name    = "E-New Error 1";
                        pre     = "";
                        post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value v ^ ", " ^ string_of_mem mem;
                    }
                )
            )

            (** se `e` for um valor, defina um novo local na memória e associe o valor de `e` ao local na memória *)
            else
                (* ordene a memória por posição *)
                let mem' = sort mem in

                (* associe `v` a um novo local na memória *)
                let l = where mem' in match value_of_term e with
                | Some v -> 
                    let mem'' = set l v mem' in

                    (* retorne `l` enquanto termo *)
                    (Term (Location l), table, mem'', {
                        name    = "E-New 1";
                        pre     = "";
                        post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (Location l) ^ ", " ^ string_of_mem mem''
                    })
                | None -> Value (EvaluationError ("Nao foi possivel avaliar " ^ ast_of_term e)),
                    table, mem, {
                        name = "E-New Error";
                        pre  = "";
                        post = "";
                    }
            )

        
        (** if(e1, e2, e3) Conditional
            avaliação da esquerda para direita:

            se e1 não for um valor, avalie-o até que seja;
            se e1 for verdadeiro, então retorne e2;
            se e1 for falso     , então retorne e3
            [se e1 for um valor não booleano, erro]
        *)
        | Conditional (e1, e2, e3) ->(
            (** e1 -> e1' => if(e1, e2, e3) -> if(e1', e2, e3) *)
            if not (is_value_term e1) then(
                (match step e1 table mem with
                    |   Term e1', _, _, _ -> step (Conditional (e1', e2, e3)) table mem
                    |   Value v, _, _, _ -> Value (EvaluationError "Erro ao avaliar um termo"), table, mem, {
                        name    = "E-If Error 1";
                        pre     = "";
                        post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value v ^ ", " ^ string_of_mem mem;
                    }))
            else(
                match value_of_term e1 with
                | Some (VBoolean true) -> step e2 table mem
                | Some (VBoolean false) -> step e3 table mem
                | _ -> Value (EvaluationError "Erro ao avaliar um termo"), table, mem, {
                    name    = "E-If Error 2";
                    pre     = "";
                    post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value (EvaluationError "Erro ao avaliar um termo") ^ ", " ^ string_of_mem mem;
                }))
        
        (** e1; e2
        Sequência
        
        Sequence (e1, e2)
        `e1` deve ser avaliado até que se torne Unit.
        Quando `e1` = Unit, então `Sequence (Unit, e2)` é avaliado para `e2`
        *)
        | Sequence (e1, e2) ->(
            (** e1 -> e1' => Sequence(e1, e2) => Sequence(e1', e2) *)
            if not (is_value_term e1) then
                (match step e1 table mem with
                    |   Term e1', _, _, _ -> step (Sequence (e1', e2)) table mem
                    |   Value v, _, _, _ -> Value (EvaluationError "Erro ao avaliar um termo"), table, mem, {
                        name    = "E-Sequence Error 1";
                        pre     = "";
                        post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value v ^ ", " ^ string_of_mem mem;
                    })
            else
                match value_of_term e1 with
                | Some VUnit -> step e2 table mem
                | _ -> Value (EvaluationError ("`e1` deve ser avaliado para Unit em uma sequência `e1; e2`")), table, mem, {
                    name    = "E-Seq Error";
                    pre     = "";
                    post    = "";
                })
        
        (** while e1 do e2
            comando while é avaliado expandindo-o para um if com e1, e2 e Unit
            *)
        | While (e1, e2) ->(
            let expanded = Conditional (e1, Sequence (e2, While (e1, e2)), Unit) in
            Term (expanded), table, mem, {
                name    = "E-While";
                pre     = "";
                post    = ast_of_term e ^ ", " ^ string_of_mem  mem ^ " -> " ^ ast_of_term expanded ^ ", " ^ string_of_mem mem
            })

        (** operações binárias:
        avaliação da esquerda para a direita:

        se o primeiro termo (e1) não for um valor, avalie-o até que seja
        se o segundo termo (e2) não for um valor, avalie-o até que seja 
        quando ambos termos forem valores, tente fazer a operação binária *)
        | BinaryOperation (op, e1, e2) ->(
            (** se `e1` não for um valor, isto é, se for possível dar um passo e1 -> e1', então tente dar um passo. *)
            if not (is_value_term e1) then
                (match step e1 table mem  with
                    (* e1 -> e1' => e1 op e2 -> e1' op e2. *)
                        | Term e1', _, _, _ -> step (BinaryOperation (op, e1', e2)) table mem
                        | Value v, _, _, _ -> Value (EvaluationError "Erro ao avaliar um termo"), table, mem, {
                            name    = "E-BinOp Error 1";
                            pre     = "";
                            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value v ^ ", " ^ string_of_mem mem;
                        }
                )
            (** se `e1` = `v1` for um valor, mas `e2` não for um valor, então tente dar um passo e2 -> e2'. *)
            else if not (is_value_term e2) then
                (match step e2 table mem with
                    (** e2 -> e2' => e1 op e2 -> e1 op e2'. *)
                    | Term e2', _, _ , _ -> step (BinaryOperation (op, e1, e2')) table mem
                    | Value v, _, _, _ -> Value (EvaluationError "Erro ao avaliar um termo"), table, mem, {
                        name    = "E-BinOp Error 2";
                        pre     = "";
                        post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value v ^ ", " ^ string_of_mem mem;
                    }
                )
            (** são valores `e1` = `v1` e `e2` = `v2`. *)
            else (match (value_of_term e1, value_of_term e2) with
                    | (Some v1, Some v2) ->
                        (** aplique a função para computar o resultado de uma operação binária. *)
                        let result_value = apply_binop op v1 v2 in
                        
                        (** apply_binop sempre retorna um valor.
                            pdoe ser um valor real, ou um erro (EvaluationError) *)
                        (match result_value with 
                            |   EvaluationError s -> (Value (EvaluationError s), table, mem, {
                                    name = "E-Binop Error";
                                    pre  = "";
                                    post = s;
                            })

                            |   v -> Value v, table, mem, {
                                name    = "E-Binop";
                                pre     = "";
                                post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value v ^ ", " ^ string_of_mem mem;
                            }
                        )

                    | _ -> Value (EvaluationError ("Erro ao avaliar um termo, e=" ^ ast_of_term e)), table, mem, {
                        name    = "E-BinOp Error 3";
                        pre     = "";
                        post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value (EvaluationError "Erro ao avaliar um termo") ^ ", " ^ string_of_mem mem;
                    }
            ))


        | _ -> (Value (EvaluationError "Não Implementado"), table, mem, {
            name    = "E-Error";
            pre     = "T";
            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> $" ^ string_of_value (EvaluationError "Não Implementado") ^ ", " ^ string_of_mem mem;
        })
;;

(** `stepn` avalia um termo até que retorne um valor ou um erro.
    `limit` representa o limite de passos de avaliação

    avalia o termo `e` sobre uma memória `mem` e uma tabela de símbolos `table`
    até que `e` resulte em um valor, ou que `limit` seja atingido.

    retorna sempre      um valor (forma normal, ou erro),
            além de     tabela de símbolos e memória, possivelmente atualizadas        
*)
let rec stepn       (e       :       term)
                    (mem    :     memory)
                    (table  :    symbols)
                    (limit  :        int)
                    (rules  : evaluation)
                        :   (value * symbols * memory * evaluation) =
    if (limit <= 0) then ((EvaluationError "limite de passos atingido"), table, mem, rules)
    else
        match step e table mem with
            | (Value v, t, m, r)    -> (v, t, m, r :: rules)
            | (Term e', t, m, r)    -> stepn e' m t (limit - 1) (r :: rules)
    ;;

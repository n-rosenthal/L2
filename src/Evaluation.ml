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

(** substitui um termo `x` por um valor `y` em um termo `e`
    Implementação para expressões Let (x, [t], e1, e2) = (x, [t], y, e) *)
let rec substitute (x: string) (y: term) (e: term) : term =
        match e with
        | Integer _ | Boolean _ | Unit | Location _ -> e
        | Identifier s -> if s = x then y else e
        | Conditional (a, b, c) -> Conditional (substitute x y a, substitute x y b, substitute x y c)
        | BinaryOperation (op, a, b) -> BinaryOperation (op, substitute x y a, substitute x y b)
        | While (a, b) -> While (substitute x y a, substitute x y b)
        | Assignment (l, r) -> Assignment (substitute x y l, substitute x y r)
        | Let (s, t, a, b) -> if s = x then Let (s, t, substitute x y a, b) else Let (s, t, substitute x y a, substitute x y b)
        | New a -> New (substitute x y a)
        | Dereference a -> Dereference (substitute x y a)
        | Sequence (a, b) -> Sequence (substitute x y a, substitute x y b)
;;


(** ---
    Avaliação de termos
    ---
*)

(** faz um passo na avaliação de um termo, se for possível *)
let rec step    (e     :     term)
                (table :  symbols)
                (mem   :   memory)
                :   (term * symbols * memory * rule,
                    value * symbols * memory * rule) result =
    match e with
        (* valores são formais normais e não são avaliados *)
        | Integer n -> Error (VInteger n, table, mem,
                                {name = "E-Int"; pre = ""; post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value (VInteger n) ^ ", " ^ string_of_mem mem}
                            )

        | Boolean b -> Error (VBoolean b,
                                table,
                                mem,
                                {name = "E-Bool"; pre = ""; post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value (VBoolean b) ^ ", " ^ string_of_mem mem}
                            )

        | Unit      -> Error (VUnit,
                            table,
                            mem,
                            {name = "E-Unit"; pre = ""; post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value (VUnit) ^ ", " ^ string_of_mem mem}
                        )
        
        (** operações binárias:
            avaliação da esquerda para a direita:

            se o primeiro termo (e1) não for um valor, avalie-o até que seja
            se o segundo termo (e2) não for um valor, avalie-o até que seja 
            quando ambos termos forem valores, tente fazer a operação binária *)
        | BinaryOperation (op, e1, e2) ->
            (** se `e1` não for um valor, isto é, se for possível dar um passo e1 -> e1', então tente dar um passo. *)
            if not (is_value_term e1) then
                (match step e1 table mem  with
                    (** e1 !-> e1', erro. *)
                    | Error s -> Error s

                    (** e1 -> e1' => e1 op e2 -> e1' op e2. *)
                    | Ok (e1', table', mem', r) -> 
                        Ok (BinaryOperation (op, e1', e2),
                            table',
                            mem',
                            {name   = "E-BinOp" ^ string_of_binary_operator op ^ " 1";
                            pre     = ast_of_term e1 ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term e1' ^ ", " ^ string_of_mem mem';
                            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (BinaryOperation (op, e1', e2)) ^ ", " ^ string_of_mem mem'}))
            (** se `e1` = `v1` for um valor, mas `e2` não for um valor, então tente dar um passo e2 -> e2'. *)
            else if not (is_value_term e2) then
                (match step e2 table mem with
                    (** e2 !-> e2', erro. *)
                    | Error s -> Error s

                    (** e2 -> e2' => e1 op e2 -> e1 op e2'. *)
                    | Ok (e2', table', mem', r) -> 
                        Ok (BinaryOperation (op, e1, e2'),
                            table',
                            mem',
                            {name   = "E-Binop" ^ string_of_binary_operator op ^ " 2";
                            pre     = ast_of_term e2 ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term e2' ^ ", " ^ string_of_mem mem';
                            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (BinaryOperation (op, e1, e2')) ^ ", " ^ string_of_mem mem'}))

            (** são valores `e1` = `v1` e `e2` = `v2`. *)
            else (match (value_of_term e1, value_of_term e2) with
                    | (Some v1, Some v2) ->
                        (** aplique a função para computar o resultado de uma operação binária. *)
                        let result_value = apply_binop op v1 v2 in
                        
                        (** apply_binop sempre retorna um valor.
                            pdoe ser um valor real, ou um erro (EvaluationError) *)
                        (match result_value with 
                            |   EvaluationError s -> Error (EvaluationError s, table, mem, {
                                    name = "E-Binop Error";
                                    pre  = "";
                                    post = s;
                            })

                            |   v -> Error (v, table, mem, {
                                    name = "E-Binop";
                                    pre  = ast_of_term e1 ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value v1 ^ ", " ^ string_of_mem mem ^ ", " ^
                                            ast_of_term e2 ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value v2 ^ ", " ^ string_of_mem mem ^ ", ";
                                    post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value v ^ ", " ^ string_of_mem mem;
                            })
                        )
                    
                    |  _ -> Error (EvaluationError ("Não foi possível avaliar " ^ ast_of_term e),
                            table, mem,
                            {name = "E-Binop Error 1";
                            pre     = "";
                            post    = "";
                            })
            )


        (** if(e1, e2, e3) Conditional
            avaliação da esquerda para direita:

            se e1 não for um valor, avalie-o até que seja;
            se e1 for verdadeiro, então retorne e2;
            se e1 for falso     , então retorne e3
            [se e1 for um valor não booleano, erro]
        *)
        | Conditional (e1, e2, e3) ->
            (** e1 -> e1' => if(e1, e2, e3) -> if(e1', e2, e3) *)
            if not (is_value_term e1) then
                (match step e1 table mem with
                (** e1 !-> e1' => erro *)
                | Error s -> Error s
                
                (** e1 -> e1' => if(e1, e2, e3) -> if(e1', e2, e3) *)
                | Ok (e1', table', mem', r) -> 
                    Ok  (Conditional (e1', e2, e3), 
                        table',
                        mem', 
                        {name   = "E-If 3";
                        pre     =   ast_of_term e1 ^ ", " ^ string_of_mem mem ^ " -> " ^
                                    ast_of_term e1' ^  ", " ^ string_of_mem mem';
                        post    =   ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^
                                    ast_of_term (Conditional (e1', e2, e3)) ^  ", " ^ string_of_mem mem'}))
            else
                (* `e1` = `v1` é um valor *)
                (match value_of_term e1 with
                    (** se `v1` for verdadeiro, então retorne `e2`. *)
                    | Some (VBoolean true) -> Ok (e2, table, mem, {
                        name    = "E-If (1) True";
                        pre     = "";
                        post    = "if true then " ^ ast_of_term e2 ^ " else " ^ ast_of_term e3 ^ ", " ^ string_of_mem mem ^ " -> " ^ 
                                    ast_of_term e2 ^ ", " ^ string_of_mem  mem})

                    (** se `v1` for falso, então retorne `e3`. *)
                    | Some (VBoolean false) -> Ok (e3, table, mem, {
                        name    = "E-If (2) False";
                        pre     = "";
                        post    = "if false then " ^ ast_of_term e2 ^ " else " ^ ast_of_term e3 ^ ", " ^ string_of_mem mem ^ " -> " ^ 
                                    ast_of_term e3 ^ ", " ^ string_of_mem  mem})

                    (** se `v1` for um valor não booleano, erro. *)
                    | _ -> Error (EvaluationError ("Não foi possivel avaliar " ^ ast_of_term e),
                        table, mem,
                        {name = "E-If Error";
                        pre  = "";
                        post = "";
                        })
                )

        (* e1; e2   Sequence
            Sequência
            `e1` deve ser avaliado até que se torne Unit.
            Quando `e1` = Unit, então `Sequence (Unit, e2)` é avaliado para `e2` *)
        | Sequence (e1, e2) ->
            (** se `e1` não for um valor, avalie-o até que seja *)
            if not (is_value_term e1) then
                (match step e1 table mem with
                (** e1 -> e1' => e1; e2 -> e1'; e2. *)
                | Ok (e1', table', mem', r) -> Ok (Sequence (e1', e2), 
                                            table',
                                            mem', 
                                            {name   = "E-Sequence";
                                            pre     = ast_of_term e1 ^ ", " ^ string_of_mem mem ^ " -> " ^ 
                                                        ast_of_term e1' ^ ", " ^ string_of_mem mem';
                                            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^
                                                        ast_of_term (Sequence (e1', e2)) ^ ", " ^ string_of_mem mem'}))
            else (match value_of_term e1 with
                (** se `e1` = Unit, então `Sequence (Unit, e2)` é avaliado para `e2` *)
                | Some VUnit -> Ok   (e2,
                                    table,
                                    mem,
                                    {name   = "E-Sequence 1";
                                    pre     = "";
                                    post    = "(); " ^ ast_of_term e2 ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term e2 ^ ", " ^ string_of_mem mem}))
                | _ -> Error (EvaluationError ("`e1` deve ser avaliado para Unit em uma sequência `e1; e2`"),
                    table, mem, {name = "E-Seq Error"; pre = ""; post = ""})
            
    
        (** while e1 do e2
            comando while é avaliado expandindo-o para um if com e1, e2 e Unit *)
        | While (e1, e2) ->
            let expanded = Conditional (e1, Sequence (e2, While (e1, e2)), Unit) in
            Ok (expanded,
                table,
                mem, 
                {name   = "E-While";
                pre     = "";
                post    = ast_of_term e ^ ", " ^ string_of_mem  mem ^ " -> " ^ ast_of_term expanded ^ ", " ^ string_of_mem mem })

    
        (** Identificador x
            Variáveis.
            
            Um identificador é avaliado para um valor armazenado na memória. 
            
            Identifier x -> (Dereference (Location l)) *)
        | Identifier x -> 
            (* acessa a tabela de símbolos para verificar se `x` está lá *)
            if is_bound x table then
                match search x table with
                | Some l -> Ok (Dereference (Location l), table, mem, {
                    name    = "E-Id";
                    pre     = "";
                    post    = x ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (Dereference (Location l)) ^ ", " ^ string_of_mem mem})
                | None -> Error (EvaluationError ("Identificador não declarado: `" ^ x ^ "`"),
                    table, mem,
                    {name = "E-Id Error";
                    pre  = "";
                    post = "";
                    })
            else Error (EvaluationError ("Identificador não declarado: `" ^ x ^ "`"),
                table, mem, {
                    name = "E-Id Error";
                    pre  = "";
                    post = "";
                })

        (** Dereferência
            !e : recupera o valor que está na posição de memória que `e` aponta 
            
            `e` deve ser (VLocation l) *)
        | Dereference e ->
            (** avaliação esq. -> dir.;
                se `e` não é um valor, então avalie-o até que seja *)
            if not (is_value_term e) then (match step e table mem with
                | Ok (e', table', mem', r) -> Ok (Dereference e', table', mem', {
                        name    = "E-Deref";
                        pre     = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term e' ^ ", " ^ string_of_mem mem';
                        post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (Dereference e') ^ ", " ^ string_of_mem mem'}))
                
            (** se for um valor, então verifique se é uma VLocation l *)
            else (match value_of_term e with
                (** `e` é um valoe e `e` = `l` é uma localização na memória *)
                | Some (VLocation l) -> (
                    (** verifique se a posiçãao `l` realmente existe na memória *)
                    if (exists l mem) then
                        (** se existir, então recupere o valor associado à `l` na memória
                            pois este é o valor apontado pela variável `e` (Identifier x) *)
                        (match get l mem with
                            |   Some v -> (match term_of_value v with
                                |   Some t -> Ok (t, table, mem, {
                                    name    = "E-Deref 1";
                                    pre     = "";
                                    post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term t ^ ", " ^ string_of_mem mem})

                                |   None -> Error (EvaluationError ("Nao foi possivel avaliar " ^ ast_of_term e),
                                    table, mem,
                                    {name = "E-Deref Error";
                                    pre  = "";
                                    post = "";
                                    })))
                    else Error (EvaluationError ("Nao foi possivel avaliar " ^ ast_of_term e),
                        table, mem,
                        {name = "E-Deref Error";
                        pre  = "";
                        post = "";
                        })))

(** `stepn` avalia um termo até que retorne um valor ou um erro.

    em `step` :
    isto é feito tratanto tanto erros reais quanto valores como Error em um objeto result;
    dessa forma, temos  Ok (term, ...)      enquanto a avaliação está ocorrendo, e
                        Error (value, r)    quando a avaliação para, por algum motivo.
    
    tanto durante a avaliação quanto quando acaba a avaliação,
    são passados objetos tabela de símbolos e memória e a regra de avaliação usada.

    aqui, em `stepn`:
    o tipo resultado é  Ok          (termo, tabela de símbolos, regra)
                        ou Error    (mensagem de erro)
    porque queremos imprimir termos ou strings no interpretador.

    uma `evaluation` é uma lista de regras, aliás `rule list`.
*)
let rec stepn       (e       :       term)
                    (mem    :     memory)
                    (table  :    symbols)
                    (limit  :        int)
                    (rules  : evaluation)
                        :   (term * symbols * memory * evaluation, 
                            value * symbols * memory * evaluation) result =
    if (limit <= 0) then Error (EvaluationError "limite de passos atingido", table, mem, rules)
    else
        match step e table mem with
            | Error (v, t, m, r)    -> Error (v, t, m, r :: rules)
            | Ok (e', t, m, r)      -> stepn e' m t (limit - 1) (r :: rules)
;;
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
        | Derefence a -> Derefence (substitute x y a)
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
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

(** converte valor para termo, falha com exceção se não for possível *)
(** converte valor para termo, falha com exceção se não for possível *)
let term_of_value_exn = function
    | VInteger n -> Integer n
    | VBoolean b -> Boolean b
    | VUnit -> Unit
    | VLocation l -> Location l
    | EvaluationError s -> failwith ("Não pode converter erro para termo: " ^ s)

(** verifica se um termo representa um valor *)
let is_value_term = function
    | Integer _ | Boolean _ | Unit | Location _ -> true
    | _ -> false

(** converte um termo para um valor *)
let value_of_term = function
    | Integer n -> Some (VInteger n)
    | Boolean b -> Some (VBoolean b)
    | Unit -> Some VUnit
    | Location l -> Some (VLocation l)
    | _ -> None

(** converte um valor para um termo *)
let term_of_value = function
    | VInteger n -> Some (Integer n)
    | VBoolean b -> Some (Boolean b)
    | VUnit -> Some Unit
    | VLocation l -> Some (Location l)
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
*)
let rec substitute (x : string) (v : value) (e : term) : term =
    match e with
    | Identifier s when s = x -> term_of_value_exn v
    | Identifier s -> Identifier s
    | Integer n -> Integer n
    | Boolean b -> Boolean b
    | Unit -> Unit
    | Location l -> Location l
    | BinaryOperation (op, e1, e2) ->
        BinaryOperation (op, substitute x v e1, substitute x v e2)
    | Conditional (e1, e2, e3) ->
        Conditional (substitute x v e1, substitute x v e2, substitute x v e3)
    | Let (id, t, e1, e2) ->
        if id = x then
            Let (id, t, substitute x v e1, e2)
        else
            Let (id, t, substitute x v e1, substitute x v e2)
    | Sequence (e1, e2) ->
        Sequence (substitute x v e1, substitute x v e2)
    | While (cond, body) ->
        While (substitute x v cond, substitute x v body)
    | Assignment (e1, e2) ->
        Assignment (substitute x v e1, substitute x v e2)
    | Dereference e1 -> Dereference (substitute x v e1)
    | New e1 -> New (substitute x v e1)

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
let rec step (e : term) (table : symbols) (mem : memory) 
    : step_result * symbols * memory * rule =
    match e with
    (** Valores: não precisam de mais avaliação *)
    | Integer n -> (Value (VInteger n), table, mem, {
        name = "E-Int";
        pre = "";
        post = string_of_int n;
    })
    
    | Boolean b -> (Value (VBoolean b), table, mem, {
        name = "E-Bool";
        pre = "";
        post = string_of_bool b;
    })
    
    | Unit -> (Value VUnit, table, mem, {
        name = "E-Unit";
        pre = "";
        post = "()";
    })
    
    | Location l -> (Value (VLocation l), table, mem, {
        name = "E-Loc";
        pre = "";
        post = "ℓ" ^ string_of_int l;
    })

    (** Identificador: procura na tabela de símbolos *)
    | Identifier x -> (
        match search x table with
        | Some l -> (Value (VLocation l), table, mem, {
            name = "E-Id";
            pre = "";
            post = x ^ " → ℓ" ^ string_of_int l;
        })
        | None -> (Value (EvaluationError ("Identificador não declarado: " ^ x)), 
                   table, mem, {
            name = "E-Id-Error";
            pre = "";
            post = "";
        })
    )

    (** New: aloca memória *)
    | New e -> (
        match step e table mem with
        | (Value v, new_table, new_mem, r) ->
            let mem_sorted = sort new_mem in
            let l = where mem_sorted in
            let mem_new = set l v mem_sorted in
            (Value (VLocation l), new_table, mem_new, {
                name = "E-New";
                pre = "";
                post = "new " ^ string_of_value v ^ " → ℓ" ^ string_of_int l;
            })
        | (Term _, _, _, _) -> 
            (* Isso não deveria acontecer se step for implementado corretamente *)
            (Value (EvaluationError "Erro interno em New"), table, mem, {
                name = "E-New-Error";
                pre = "";
                post = "";
            })
    )

    (** Dereference: acessa memória *)
    | Dereference e -> (
        match step e table mem with
        | (Value (VLocation l), new_table, new_mem, r) ->
            (match get l new_mem with
            | Some v -> (Value v, new_table, new_mem, {
                name = "E-Deref";
                pre = "";
                post = "!ℓ" ^ string_of_int l ^ " → " ^ string_of_value v;
            })
            | None -> (Value (EvaluationError "Localização inválida"), new_table, new_mem, {
                name = "E-Deref-Error";
                pre = "";
                post = "";
            }))
        | (Value _, new_table, new_mem, _) ->
            (Value (EvaluationError "Deref de não-localização"), new_table, new_mem, {
                name = "E-Deref-Type-Error";
                pre = "";
                post = "";
            })
        | (Term _, _, _, _) ->
            (* Isso não deveria acontecer *)
            (Value (EvaluationError "Erro interno em Deref"), table, mem, {
                name = "E-Deref-Error";
                pre = "";
                post = "";
            })
    )

    (** Let: associação de valor a identificador *)
    | Let (x, typ, e1, e2) -> (
        match step e1 table mem with
        | (Value v1, table1, mem1, r1) ->
            (match typ with
            | Reference _ ->
                (* Para referências: v1 deve ser VLocation *)
                (match v1 with
                | VLocation l ->
                    let table' = extend x l table1 in
                    (Term e2, table', mem1, {
                        name = "E-Let-Ref";
                        pre = "";
                        post = "let " ^ x ^ " = ℓ" ^ string_of_int l ^ " in ...";
                    })
                | _ -> (Value (EvaluationError "Valor não é localização para referência"), 
                        table1, mem1, {
                        name = "E-Let-Ref-Error";
                        pre = "";
                        post = "";
                    }))
            | _ ->
                (* Para valores não-referência: substitui *)
                let e2' = substitute x v1 e2 in
                (Term e2', table1, mem1, {
                    name = "E-Let-Subst";
                    pre = "";
                    post = "let " ^ x ^ " = " ^ string_of_value v1 ^ " in ...";
                }))
        | (Term e1', table1, mem1, r1) ->
            (Term (Let (x, typ, e1', e2)), table1, mem1, {
                name = "E-Let-Step";
                pre = "";
                post = "let " ^ x ^ " = " ^ ast_of_term e1' ^ " in ...";
            })
    )

    (** Assignment: atribuição *)
    | Assignment (e1, e2) -> (
        match step e1 table mem with
        | (Value (VLocation l), table1, mem1, r1) ->
            (match step e2 table1 mem1 with
            | (Value v2, table2, mem2, r2) ->
                let m' = set l v2 mem2 in
                (Value VUnit, table2, m', {
                    name = "E-Assign";
                    pre = "";
                    post = "ℓ" ^ string_of_int l ^ " := " ^ string_of_value v2 ^ " → ()";
                })
            | (Term e2', table2, mem2, r2) ->
                (Term (Assignment (Location l, e2')), table2, mem2, {
                    name = "E-Assign-Step-R";
                    pre = "";
                    post = "ℓ" ^ string_of_int l ^ " := " ^ ast_of_term e2' ^ " → ...";
                }))
        | (Term e1', table1, mem1, r1) ->
            (Term (Assignment (e1', e2)), table1, mem1, {
                name = "E-Assign-Step-L";
                pre = "";
                post = ast_of_term e1' ^ " := " ^ ast_of_term e2 ^ " → ...";
            })
        | (Value _, table1, mem1, _) ->
            (Value (EvaluationError "Atribuição a não-localização"), table1, mem1, {
                name = "E-Assign-Type-Error";
                pre = "";
                post = "";
            })
    )

    (** BinaryOperation: operações binárias *)
    | BinaryOperation (op, e1, e2) -> (
        match step e1 table mem with
        | (Value v1, table1, mem1, r1) ->
            (match step e2 table1 mem1 with
            | (Value v2, table2, mem2, r2) ->
                let result = apply_binop op v1 v2 in
                (Value result, table2, mem2, {
                    name = "E-BinOp";
                    pre = "";
                    post = string_of_value v1 ^ " " ^ string_of_binary_operator op ^ " " ^ 
                           string_of_value v2 ^ " → " ^ string_of_value result;
                })
            | (Term e2', table2, mem2, r2) ->
                (Term (BinaryOperation (op, term_of_value_exn v1, e2')), table2, mem2, {
                    name = "E-BinOp-Step-R";
                    pre = "";
                    post = string_of_value v1 ^ " " ^ string_of_binary_operator op ^ " " ^ 
                           ast_of_term e2' ^ " → ...";
                }))
        | (Term e1', table1, mem1, r1) ->
            (Term (BinaryOperation (op, e1', e2)), table1, mem1, {
                name = "E-BinOp-Step-L";
                pre = "";
                post = ast_of_term e1' ^ " " ^ string_of_binary_operator op ^ " " ^ 
                       ast_of_term e2 ^ " → ...";
            })
    )

    (** Conditional: if-then-else *)
    | Conditional (cond, e1, e2) -> (
        match step cond table mem with
        | (Value (VBoolean true), table1, mem1, r) ->
            (Term e1, table1, mem1, {
                name = "E-If-True";
                pre = "";
                post = "if true then ... else ... → " ^ ast_of_term e1;
            })
        | (Value (VBoolean false), table1, mem1, r) ->
            (Term e2, table1, mem1, {
                name = "E-If-False";
                pre = "";
                post = "if false then ... else ... → " ^ ast_of_term e2;
            })
        | (Value _, table1, mem1, _) ->
            (Value (EvaluationError "Condição não booleana"), table1, mem1, {
                name = "E-If-Type-Error";
                pre = "";
                post = "";
            })
        | (Term cond', table1, mem1, r) ->
            (Term (Conditional (cond', e1, e2)), table1, mem1, {
                name = "E-If-Step";
                pre = "";
                post = "if " ^ ast_of_term cond' ^ " then ... else ...";
            })
    )

    (** Sequence: sequência *)
    | Sequence (e1, e2) -> (
        match step e1 table mem with
        | (Value VUnit, table1, mem1, r) ->
            (Term e2, table1, mem1, {
                name = "E-Seq";
                pre = "";
                post = "(); ... → " ^ ast_of_term e2;
            })
        | (Value _, table1, mem1, _) ->
            (Value (EvaluationError "Sequência requer Unit"), table1, mem1, {
                name = "E-Seq-Type-Error";
                pre = "";
                post = "";
            })
        | (Term e1', table1, mem1, r) ->
            (Term (Sequence (e1', e2)), table1, mem1, {
                name = "E-Seq-Step";
                pre = "";
                post = ast_of_term e1' ^ "; " ^ ast_of_term e2;
            })
    )

    (** While: expansão para if *)
    | While (cond, body) ->
        let expanded = Conditional (cond, Sequence (body, While (cond, body)), Unit) in
        (Term expanded, table, mem, {
            name = "E-While-Expand";
            pre = "";
            post = "while " ^ ast_of_term cond ^ " do " ^ ast_of_term body ^ 
                   " → if " ^ ast_of_term cond ^ " then (" ^ ast_of_term body ^ "; while ...) else ()";
        })

    (** Erro: termo não reconhecido *)
    | _ -> (Value (EvaluationError "Termo não implementado"), table, mem, {
        name = "E-Error";
        pre = "";
        post = "";
    })

(** `stepn` avalia um termo até que retorne um valor ou um erro.
    `limit` representa o limite de passos de avaliação

    avalia o termo `e` sobre uma memória `mem` e uma tabela de símbolos `table`
    até que `e` resulte em um valor, ou que `limit` seja atingido.

    retorna sempre      um valor (forma normal, ou erro),
            além de     tabela de símbolos e memória, possivelmente atualizadas        
*)
let rec stepn (e : term) (mem : memory) (table : symbols) (limit : int) 
    : (value * symbols * memory * evaluation) =
    if limit <= 0 then 
        (EvaluationError "Limite de passos atingido", table, mem, [])
    else
        match step e table mem with
        | (Value v, new_table, new_mem, r) -> 
            (v, new_table, new_mem, [r])
        | (Term e', new_table, new_mem, r) -> 
            let (v, final_table, final_mem, rules) = stepn e' new_mem new_table (limit - 1) in
            (v, final_table, final_mem, r :: rules)
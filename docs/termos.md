#   Sintaxe de termos

```ocaml
(** sintaxe de termos sobre `L2` *)
type term =
    | Integer of int                                (* n, termo número inteiro *)
    | Boolean of bool                               (* b, termo booleano *)
    | Identifier of string                          (* x, identificador *)
    | Conditional of term * term * term             (* If, operador condicional *)
    | BinaryOperation of binary_operator * term * term    (* bop, operação binária *)
    | While of term * term                          (* While e1 do e2 *)
    | Assignment of term * term                     (* x := e *)
    | Let of string * tipo * term * term            (* let x: T = e1 in e2 *)
    | New of term                                   (* new e *)
    | Derefence of term                             (* !e *)
    | Unit                                          (* () *)
    | Sequence of term * term                       (* e1; e2 *)
    | Location of int                               (* l, local de memória *)
and binary_operator = 
      | Add | Sub | Mul | Div                       (* operadores aritméticos *)
      | Eq  | Neq | Lt  | Leq | Gt | Geq            (* operadores relacionais *)
      | And | Or                                    (* operadores lógicos *)
;;
```


##  Valores
Ver `src/Terms.ml`

Não existem propriamente *regras de avaliação* para *valores*, uma vez que valores são termos já avaliados; são formais normais ou paradas, *stuck*. 

São valores os termos

```ocaml
type term = ..
    | Integer of int        (*  termo número inteiro *)
    | Boolean of bool       (*  termo booleano *)
    | Unit                  (*  termo unitário *)
    | Location of int       (*  local de memória *)
```

Estes termos são imediatamente avaliados para seus respectivos valores.

```ocaml
(** sintaxe de valores sobre `L2` *)
type value =
    | VInteger of int                               (* n, valor número inteiro *)
    | VBoolean of bool                              (* b, valor booleano *)
    | VUnit                                         (* (), unit *)
    | VLocation of int                              (* l, local de memória *)
    | EvaluationError of string                     (* s, erro de avaliação *)
and name_binding = string * value                   (* associação entre um identificador e um valor *)
;;
```

O termo `Location` e o valor `VLocation` são discutidos `docs/outras_coisas.md`#memória.

Note que `EvaluationError` não é um termo da linguagem $L_2$. Ao contrário, `EvaluationError` é definido somente na sintaxe dos *valores*. `EvaluationError` não é um valor da linguagem `L_2`, também, mas é o valor resultante da avaliação de um termo mal-formado ou que a avaliação falhou.

### Funções *helper*
1. `is_value_term`: $\text{term} \to \mathbb{B}$, verifica se um termo representa um valor.
2. `value_of_term`: $\text{term} \to \text{value} \to \mathbb{B}$, converte um termo para um valor, (caso `is_value_term e` retorne verdadeiro para `e`).
3. `term_of_value`: $\text{value} \to \text{term} \to \mathbb{B}$, converte um valor para um termo, (caso `value_of_term e` retorne verdadeiro para `e`).

### Regras de Avaliação
Artificialmente, definimos as regras de avaliação para valores, a fim de, ao imprimí-las em tela, sabermos em que ponto da avaliação foi produzido o valor.

$$
\frac{}
     {\text{Integer n}, \ \sigma \ \to \text{VInteger n}, \ \sigma}
\;(\text{E-Int})
$$

$$
\frac{}
     {\text{Boolean b}, \ \sigma \ \to \text{VBoolean b}, \ \sigma}
\;(\text{E-Bool})
$$

$$
\frac{}
     {\text{Unit}, \ \sigma \ \to \text{VUnit}, \ \sigma}
\;(\text{E-Unit})
$$

```ocaml
(** faz um passo na avaliação de um termo, se for possível *)
let rec step    (e     :    term)
                (mem   :  memory)
                : (term * memory * eval_rule, string) result =
    match e with 
    ...
    |   Integer n -> Ok (VInteger n, mem, {
                            name = "E-Int";
                            pre  = "";
                            post =  ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " 
                            ^ string_of_value (VInteger n) ^ ", " ^ string_of_mem mem
                        })
    
    |   Boolean b -> Ok (VBoolean b, mem, {
                            name = "E-Bool";
                            pre  = "";
                            post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " 
                            ^ string_of_value (VBoolean b) ^ ", " ^ string_of_mem mem
    })

    |   Unit      -> Ok (VUnit, mem, {
                            name = "E-Unit";
                            pre  = "";
                            post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " 
                            ^ string_of_value (VUnit) ^ ", " ^ string_of_mem mem
    })

    |   Location l -> Ok (VLocation l, mem, {
                            name = "E-Location";
                            pre  = "";
                            post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " 
                            ^ string_of_value (VLocation l) ^ ", " ^ string_of_mem mem
    })

    ...
```

##  Operações Binárias
Ver `src/Terms.ml`

As operações binárias implementadas são:
- op. binárias aritméticas
    -   add, sub, mul, div
- op. binárias aritméticas relacionais
    -   eq, neq, lt, leq, gt, geq
- op. binárias lógicas
    -   and, or

---
### Regras de Avaliação
Assuma o seguinte *template* para todas as regras de avaliação de operações binárias:

$$
\frac{[[v]] = [[v_1]] \ op \ [[v_2]]}
     {v_1 \ op \ v_1, \ \sigma \to v, \ \sigma}
\;(\text{E-Op})
$$

---
### Ordem de Avaliação
$L_2$ é avaliada da esquerda para a direita, então, para toda operação binária, existem as regras

$$
\frac{e_1, \sigma \ \to \ e_1', \sigma'}
    {e_1 \ op \ e_2, \ \sigma \ \to \ e_1' \ op \ e_2, \ \sigma'}
\;(\text{E-Op 1})
$$

$$
\frac{e_2, \sigma \ \to \ e_2', \sigma'}
    {v_1 \ op \ e_2, \ \sigma \ \to \ v_1 \ op \ e_2', \ \sigma'}
\;(\text{E-Op 2})    
$$

---
### Implementação
As operações binárias são **computadas** na função `apply_binop`

```ocaml
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

        | _ -> EvaluationError ("Erro de tipo para o operador binário " ^
                                (string_of_binary_operator bop) ^
                                " sobre os termos " ^ (string_of_value v1) ^ 
                                " e " ^ (string_of_value v2))
;;
```

e o valor produzido é recuperado em `step`:

```ocaml
(** faz um passo na avaliação de um termo, se for possível *)
let rec step    (e     :    term)
                (mem   :  memory)
                : (term * memory * eval_rule, string) result =
    match e with 
    ...
    | BinaryOperation (op, e1, e2) ->
                (** se `e1` não for um valor, isto é, se for possível dar um passo e1 -> e1', então tente dar um passo. *)
                if not (is_value_term e1) then
                  (match step e1 mem with
                    (** e1 !-> e1', erro. *)
                   | Error s -> Error s

                    (** e1 -> e1' => e1 op e2 -> e1' op e2. *)
                   | Ok (e1', mem', r) -> 
                        Ok (BinaryOperation (op, e1', e2),
                            mem',
                            {name   = "E-BinOp" ^ string_of_binary_operator op ^ " 1";
                            pre     = ast_of_term e1 ^ ", " ^ string_of_mem ^ mem ^ " -> " ^ ast_of_term e1' ^ ", " ^ string_of_mem ^ mem';
                            post    = ast_of_term e ^ ", " ^ string_of_mem ^ mem ^ " -> " ^ ast_of_term (BinaryOperation (op, e1', e2)) ^ ", " ^ string_of_mem ^ mem'} :: r))
                (** se `e1` = `v1` for um valor, mas `e2` não for um valor, então tente dar um passo e2 -> e2'. *)
                else if not (is_value_term e2) then
                  (match step e2 mem with
                    (** e2 !-> e2', erro. *)
                   | Error s -> Error s

                    (** e2 -> e2' => e1 op e2 -> e1 op e2'. *)
                   | Ok (e2', mem', r) -> 
                        Ok (BinaryOperation (op, e1, e2'),
                            mem',
                            {name    = "E-Binop" ^ string_of_binary_operator op ^ " 2";
                             pre     = ast_of_term e2 ^ ", " ^ string_of_mem ^ mem ^ " -> " ^ ast_of_term e2' ^ ", " ^ string_of_mem ^ mem';
                             post    = ast_of_term e ^ ", " ^ string_of_mem ^ mem ^ " -> " ^ ast_of_term (BinaryOperation (op, e1, e2')) ^ ", " ^ string_of_mem ^ mem'} :: r))
                else
                  (** são valores `e1` = `v1` e `e2` = `v2`. *)
                  (match (value_of_term e1, value_of_term e2) with
                   | (Some v1, Some v2) ->
                        (** aplique a função para computar o resultado de uma operação binária. *)
                       let result_value = apply_binop op v1 v2 in

                       (** se `result_value` for um valor, então retorne-o. *)
                       (match term_of_value result_value with
                        | Some real_value -> 
                            Ok (real_value,
                                mem,
                                {name = "E-Binop" ^ string_of_binary_operator op;
                                pre   = string_of_value rv ^ " = " ^ ast_of_term e1 ^ " " ^ string_of_binary_operator op ^ " " ^ ast_of_term e2;
                                post  = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term real_value ^ ", " ^ string_of_mem mem} :: r)
                        | None ->
                            (* runtime error value returned (EvaluationError) *)
                            let msg = (match result_value with EvaluationError s -> s | _ -> "erro de avaliação desconhecido ao longo da avaliação de uma operação binária: " ^ string_of_value result_value) in
                            Error msg)
                   | _ -> Error "Operação binária sobre termos que não podem ser avaliados")
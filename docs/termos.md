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
4. `substitute` $\text{string} \times \text{value} \times \text{term} \to \text{term}$, substitui um identificador por um valor em um termo. {x/v}e.

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

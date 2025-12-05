#   Sintaxe de Tipos para a Linguagem $L_2$
Ver: `src/Types.ml`.

Existem, em `L2`, os seguintes tipos:

-   `Int`, números inteiros
-   `Bool`, booleanos
-   `Unit`, unit (`()`, "void")
-   `Reference t`, referência para um valor de tipo `t`

```ocaml
type tipo = 
    | Int
    | Bool
    | Unit
    | Reference of tipo
    | ErrorType of string
;;
```

A fim de garantir a totalidade trivial (ou degenerada) do algoritmo de inferência estática de tipos, foi introduzido `ErrorType`, que representa um erro de tipagem obtido durante a inferência. Por exemplo, 

```
if (1) then true else false : ErrorType "O tipo da condição `e1` deve ser um booleano, mas foi `Int`"
```

Isso garante *apenas* que a inferência terminará. Não é uma garantia de que para todo termo tipável sobre $L_2$, o algoritmo `typeinfer e` será capaz de derivar o tipo de `e`.

##  `Int`, números inteiros
### Esquema de Regra Abstrata
$$
\frac{}
     {\Gamma \vdash e : \text{int}}
\;(\text{T-Int})
$$

---
### Inferência de Tipo
```ocaml
    let rec typeinfer (e: term) (env: ambiente) : tipo = (match e with 
        (** int n, número inteiro *)
        | Integer _ -> Int

        ...
    );;
```

isto é, qualquer **termo** inteiro (`Integer n`) tem o tipo `Int`. A implementação descarta o valor de `n`, pois não é importante para a tipagem; qualquer número inteiro é tipado como `Int`, etc.


---
### Regra Concreta

```ocaml
let rec infer' (e: term) (env: ambiente) (r: type_inference) : (tipo * ambiente * type_inference) = (match e with
        (** valores *)
        | Integer n -> (
            (Int, env, {
                name = "T-Int";
                requires = "T";
                ensures = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : Int";
            } :: r)
        )

        ...)
;;
```

Pré-condição: `T` (sempre verdadeiro, sem pré-condição). Pós-condição: $\Gamma \vdash e : \text{int}$.

---
##  `Bool`, booleanos
### Esquema de Regra Abstrata
$$
\frac{}
     {\Gamma \vdash e : \text{bool}}
\;(\text{T-Bool})
$$

---
### Inferência de Tipo
```ocaml
    let rec typeinfer (e: term) (env: ambiente) : tipo = (match e with
    ...
        (** b, booleano *)
        | Boolean _ -> Bool

        ...
    );;
```

isto é, qualquer **termo** booleano (`Boolean b`) tem o tipo `Bool`. A implementação descarta o valor de `b`, pois não é importante para a tipagem; qualquer booleano é tipado como `Bool`, etc.


---
### Regra Concreta

```ocaml
let rec infer' (e: term) (env: ambiente) (r: type_inference) : (tipo * ambiente * type_inference) = (match e with
    ...

        (** booleanos *)
        | Boolean b -> (
            (Bool, env, {
                name = "T-Bool";
                requires = "T";
                ensures = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : Bool";
            } :: r)
        )

        ...
    );;
```

Pré-condição: `T` (sempre verdadeiro, sem pré-condição). Pós-condição: $\Gamma \vdash e : \text{bool}$.

---
##  `Unit`, unit (`()`, "void")
### Esquema de Regra Abstrata
$$
\frac{}
     {\Gamma \vdash e : \text{unit}}
\;(\text{T-Unit})
$$

---
### Inferência de Tipo
```ocaml
    let rec typeinfer (e: term) (env: ambiente) : tipo = (match e with
    ...
        (** unit, unit *)
        | Unit -> Unit

        ...
    );;
```

---
### Regra Concreta

```ocaml
let rec infer' (e: term) (env: ambiente) (r: type_inference) : (tipo * ambiente * type_inference) = (match e with
    ...

        (** unit, unit *)
        | Unit -> (
            (Unit, env, {
                name = "T-Unit";
                requires = "T";
                ensures = string_of_env env ^ " ⊢ '" ^ ast_of_term e ^ "' : Unit";
            } :: r)
        )

        ...
    );;
```

Pré-condição: `T` (sempre verdadeiro, sem pré-condição). Pós-condição: $\Gamma \vdash e : \text{unit}$.

---
##  `Reference t`, referência para um valor de tipo `t`
Este é o único tipo não-trivial em $L_2$. Uma referência a um tipo `t`, ou `Reference t` é o tipo *apontador para tipo* `t`.


### Esquema de Regra Abstrata
$$
\frac{\Gamma \vdash e : t}
     {\Gamma \vdash \text{ref}  \ \ e : \text{ref} \ \ t}
\;(\text{T-Ref})
$$

---
### Inferência de Tipo

```ocaml
    let rec typeinfer (e: term) (env: ambiente) : tipo = (match e with
    ...
        (** ref e, aloca uma referência para um valor de tipo t *)
        | New e1 ->
            let t1 = typeinfer e1 env in
            (match t1 with
            | ErrorType msg -> ErrorType msg
            | _ -> Reference t1)

        ...
    );;
```

Explicação:

1. Primeiro inferimos t₁ = typeinfer e1 env
    1. Se t₁ for um erro, propagamos o erro
    2. Caso contrário, devolvemos Ref t₁

Assim, o tipo de `New e1` é sempre `Reference (tipo(e1))`, conforme a regra abstrata.

---
### Regra Concreta

```ocaml
let rec infer' (e: term) (env: ambiente) (r: type_inference)
    : (tipo * ambiente * type_inference) = (match e with
    ...

        (** Reference  e, aloca um valor e cria uma referência *)
        | New e1 ->
            let (t1, env1, r1) = infer' e1 env r in
            let t =
                match t1 with
                | ErrorType _ -> t1
                | _ -> Reference t1
            in
            (t, env1, {
                name = "T-New";
                requires =
                    (match t1 with
                     | ErrorType _ -> "T (erro propagado)"
                     | _ -> string_of_env env ^
                            " ⊢ '" ^ ast_of_term e1 ^ "' : " ^ string_of_type t1);
                ensures =
                    (match t with
                     | ErrorType _ -> string_of_type t
                     | _ -> string_of_env env ^
                            " ⊢ ref(" ^ ast_of_term e1 ^ ") : " ^ string_of_type t);
            } :: r1)

        ...
    );;
```

Note que a **regra que cria novas referências** é `T-New`, isto é, a regra de tipagem para o termo `new e`. Como veremos em `termos/new e`, `new e : Reference (typeinfer e)`.

Pré-condição: $\Gamma \vdash e : t$. Pós-condição: $\Gamma \vdash \text{new} \ \ e : \text{Reference} \ \ t$.

---


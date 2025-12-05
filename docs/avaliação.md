#   Avaliação de Termos
1.  `step` é a função de avaliação de termos.

```ocaml
let rec step    (e     :    term)
                (mem   :  memory)
                : (term * memory * eval_rule, string) result
```

`step e mem` é a **um passo na avaliação** de um termo `e` sobre uma memória `mem`. O resultado da avaliação é uma 3-upla de termo, memória e regra de avaliação usada para fazer `e` $\to$ `e'`.

2.  Uma **regra de avaliação** `eval_rule` é um **registro** de três componentes:

```ocaml
type eval_rule = {
    rule: string;
    pre: string;
    post: string;
}
```

que representa o *nome* da regra de avaliação, a *pré-condição* e a *pós-condição* da regra. O tipo `eval_rule` busca imitar o esquema de regra abstrata de avaliação:

$$
\frac{\text{pre}}
     {\text{post}}
\;(\text{name})
$$

3.  **Para avaliar um termo**, usamos `step` iterativamente. Existe uma função para isto: `stepn` que avalia `n` passos de um termo `e`. 

```ocaml
(**
    `stepn` avalia `n` passos de um termo `e` sobre uma memória `mem`.
*)
let rec stepn   (e      : term)
                (mem    : memory)
                (n      : int) 
                : (term * memory * evaluation, string) result =
    (** se o limite de passos for atingido, retorna um erro. *)
    if (n <= 0) then Error "step limit reached"

    (** se o termo `e` for um valor, então retorna o termo, memória e uma lista de regras de avaliação vazia. *)
    else if is_value_term e then Ok (e, mem, [])
        else
            (** se for possível dar um passo (n > 0, is_value_term e = false), tente *)
            match step e mem with
                (** se der errado, propague o erro *)
                | Error s -> Error s

                (** se der certo, chame a função recursivamente; se o resultado DESTA iteração
                    for um valor, então ele será retornado antes de `step e' mem` ser chamado sobre
                    ele; senão, (se for possível dar um passo, isso é, se não for um valor) segue ... *)
                | Ok (e', mem', r) ->
                    (** chamada recursiva *)
                    (match multi_step e' mem' (limit - 1) with
                        (** se der errado, propague o erro (novamente) *)
                        | Error s -> Error s
                    (** se der certo, retorne o termo, memória e uma regra de avaliação *)
                    | Ok (final_t, final_mem, trace) -> Ok (final_t, final_mem, (r :: trace)))
```

A função `stepn` retorna **ou** uma 3-upla de termo, memória e regra de avaliação **ou** uma mensagem de erro. É necessário fazer *pattern matching* para determinar se o resultado é uma 3-upla ou uma mensagem de erro. **Isso é feito no interpretador**. A função do interpretador é **receber os resultados da inferência de tipo e da avaliação**. Então **o interpretador** decide se deu certo ou não e **imprime o resultado**.

4. Em OCaml, um *tipo resultado* é um tipo que pode ser `Ok` ou `Error`. Entende-se que é o *resultado* de alguma operação; se a operação for bem sucedida, então será retornado um objeto do tipo `Ok t`; caso contrário, `Error` é retornado. No caso acima, `stepn` retorna um resultado de um termo, memória e uma regra de avaliação (Ok) ou uma mensagem de erro (Error).

5. O *tipo* `evaluation` representa uma **lista de regras de avaliação**. Uma regra de avaliação é um **registro**, então uma `evaluation` é uma **lista de registros**.

```ocaml
(**
    Um esquema (concreto) de regra de avaliação é definido por
        o nome do esquema de regra (rule scheme)
        a pré-condição à regra  (pre),
        a pos-condição da regra (pos)
    
    portanto a regra indicada por `name`, garante que se `pre` estiver garantido,
    então `post` seguirá. *)
    type eval_rule = {
        name:   string;
        pre:    string;
        post:   string;
    } and evaluation = eval_rule list;;


    (** mesma coisa que: *)
    type eval_rule = {
        name:   string;
        pre:    string;
        post:   string;
    };;

    type evaluation = eval_rule list;;
```

6.  Para saber sobre o interpretador e o programa principal, ver o `README.md` principal.

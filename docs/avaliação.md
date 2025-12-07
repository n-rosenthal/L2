#   Avaliação de Termos
1.  `step` é a função de avaliação de termos.

```ocaml
let rec step    (e     :    term)
                (mem   :  memory)
                : (term * memory * eval_rule, string) result
```

`step e mem` é a **um passo na avaliação** de um termo `e` sobre uma memória `mem`. O resultado da avaliação é uma 3-upla de termo, memória e regra de avaliação usada para fazer `e` $\to$ `e'`.

2.  As regras de avaliação, assim como as de inferência de tipo, são tipadas da seguinte forma:

```ocaml
(** `src/Constructions.ml` *)

type rule = {
    name:   string;
    pre:    string;
    post:   string;
}   and type_inference = rule list
    and evaluation = rule list;;
```

Note que uma regra de avaliação (`evaluation`) é uma lista de regras de avaliação, e uma regra de inferência de tipo (`type_inference`) é uma lista de regras de inferência de tipo. Etc.

As regras buscam imitar a consequência sintática:

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
```

4.  Memória e Tabela de Símbolos.

A memória foi implementada em dois passos.
    1.  Existe uma tabela de símbolos, que associa identificadores a localizações na memória;
    2.  Existe uma memória, que associa localizações a valores.

    Uma localização na memória (`location = int`) é associada a um identificador
    quando fazemos um comando `let x = e1 in e2`. Após verificar que `x` ainda não está
    na tabela de símbolos, criamos uma nova entrada na tabela e verificamos a memória
    por uma nova posição disponível. A memória fornece `l`, e registramos na tabela de símbolos
    a entrada (`x`, `l`).

    Em seguida, para o valor `e1` em `let x = e1 in e2`, avaliamos `e1` e registramos
    o resultado na memória na localização `l`. Por fim, é feita a substituição de toda
    ocorrência do identificador `x` em `e2` por `v1`, que é o valor de `e1` na memória.

    Em `src/Constructions.ml` existem mais informações sobre a memória e a tabela de símbolos,
    bem como o ambiente de tipos.

    Em `src/Evaluation.ml`, a avaliação de cada termo relacionado a memória:

        Identifier x, new e, !e, e1 := e2, let x : t = e1 in e2
    
    demonstrará os detalhes da implementação, bem como em `docs/termos.md` está descrita formalmente a avaliação e a inferência de tipo para termo em L_2.

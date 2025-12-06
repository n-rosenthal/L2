#   Inferência Estática de Tipos
1.  A inferência de tipos é feita pela função `infer e` em `src/TypeInference.ml`.

É uma função que chama a função recursiva `let rec infer' (e: term) (env: ambiente) (r: type_inference) : (tipo * ambiente * type_inference)`.

Note que, cada vez que `infer'` é chamada, é necessário fornecerum term e um ambiente de tipos. Também é passada a lista de regras de inferência obtidas até este ponto. As regras vão sendo acumuladas em uma lista, e ao final da inferência esta lista de regras é devolvida ao programador.

2.  Uma regra de inferência é um objeto do tipo

```ocaml
(** `src/Constructions.ml` *)

type rule = {
    name:   string;
    pre:    string;
    post:   string;
}   and type_inference = rule list
    and evaluation = rule list;;
```

Note que uma inferência de tipo (`type_inference`) é uma lista de regras de inferência de tipos, e uma avaliação de termos (`evaluation`) é uma lista de regras de avaliação de termos.

3. O tipo de `infer` é `infer (e: term) : tipo * type_inference`. Dado um termo `e`, `infer` retorna o tipo de `e` e a lista de regras de inferência usadas para tipá-lo.

4. O ambiente de tipos `env` é passado em todos os passos de `infer'`. O ambiente de tipos é somente uma lista de pares (identificador: string * tipo: tipo). As funções `lookup` e `put` usadas para lidar com o ambiente de tipos são definidas em `src/Constructions.ml`.
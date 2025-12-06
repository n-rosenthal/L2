1.  `src/Representations.ml`
    Representações em formato de string para termos, valores, tipos, ambiente de tipos, memória, regras de inferência de tipos e avaliação de termos. É comum que funções que retornam representação em string de um objeto, em OCaml, sejam escritas `string_of_t`, para algum tipo `t`, então `string_of_term` é uma função que recebe um `term` e retorna sua representação como `string`;

2.  `src/Constructions.ml`
    Este módulo define todas as *construções* sobre termos ou sobre tipos:
    1.  ambiente de tipos: `ambiente`;

    Um `ambiente` é uma lista de `name_binding`. Um `name_binding` é um par `string` (identificador, $\text{x}$) e um `tipo`. Com isso, **associamos** um **nome** a um **tipo**. Um **ambiente de tipos**, então´, é uma **lista de associações entre nomes e tipos**, ou
    
    ```ocaml
    type ambiente = (string * tipo) list
    ```

    Existem duas funções sobre ambientes de tipos: `lookup x env` e `put x t env`.

    `lookup x env` retorna o tipo de `x` em `env`, se `x` estiver em `env`, e `None` caso contrário. `put x t env` adiciona/atualiza (x,t) no ambiente.

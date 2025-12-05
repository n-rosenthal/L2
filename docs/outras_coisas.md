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

    2.  regras para avaliação de termos e inferência estática de tipos
    ```ocaml
    (**
        Esquema de regra concreto para inferência estática de tipos
        e para avaliação de termos
    **)
    type rule = {
        name:   string;
        pre:    string;
        post:   string;
    }   and type_inference = rule list
        and evaluation = rule list;;
    ```

    Uma regra é um registro de componentes {nome da regra, pré-condição, pós-condição}. Uma *inferência de tipo* é uma lista de regras de inferência de tipos e uma *avaliação de termos* uma lista de regras de avaliação de termos. As regras são obtidas durante a inferência/avaliação e são acumuladas pelo algoritmo. Ao final, o algoritmo retorna (além do resultado e do ambiente de tipos/memória) a lista de regras. O interpretador imprime as regras.

    3.  memória: `memory`;

    ```ocaml
    (**
    Memória para avaliação de termos
    **)
    type memory = (location * string * value) list
    and location = int;;
    ```

    Uma *memória* `memory` é uma lista de 3-uplas `(location, name, value)`, onde `location` representa um *localização* ou posição na memória, `name` representa um *identificador* ($\text{x}$, uma string) e `value` representa um *valor* (um `value`). Dessa forma, a memória é um mapeamento indexado de identificadores para valores.

    Diferente do que na inferência, um identificador é um ponteiro para um local na memória. (?)

    Existem algumas funções para lidar com a memória:

    `set mem (loc: location) (v: value) : memory`: atualiza um local na memória;
    `get mem (loc: location) : value option`: retorna o valor de um local na memória;
    `loc_of_identifier mem (x: string) : location option`: retorna a localização de um identificador na memória;
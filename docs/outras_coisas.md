1.  `src/Representations.ml`
    Representações em formato de string para termos, valores, tipos, ambiente de tipos, memória, regras de inferência de tipos e avaliação de termos. É comum que funções que retornam representação em string de um objeto, em OCaml, sejam escritas `string_of_t`, para algum tipo `t`, então `string_of_term` é uma função que recebe um `term` e retorna sua representação como `string`;

2.  `src/Constructions.ml`
    Este módulo define todas as *construções* sobre termos ou sobre tipos:


###  ambiente de tipos: `ambiente`;

Um `ambiente` é uma lista de `name_binding`. Um `name_binding` é um par `string` (identificador, $\text{x}$) e um `tipo`. Com isso, **associamos** um **nome** a um **tipo**. Um **ambiente de tipos**, então´, é uma **lista de associações entre nomes e tipos**, ou

```ocaml
type ambiente = (string * tipo) list
```

Existem duas funções sobre ambientes de tipos: `lookup x env` e `put x t env`.

`lookup x env` retorna o tipo de `x` em `env`, se `x` estiver em `env`, e `None` caso contrário. `put x t env` adiciona/atualiza (x,t) no ambiente. 

`put x t env` coloca o par `x` e `t` no ambiente `env` e retorna o ambiente resultante.

### regras de inferência de tipos e avaliação de termos

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

note que uma inferência de tipo (`type_inference`) é uma lista de regras [de inferência de tipo], e uma avaliação de termo (`evaluation`) é uma lista de regras [de avaliação de termos]. Etc.

### tabela de símbolos

```ocaml
(** localização na memória, aliás int *)
type location = int;;

(** uma tabela de símbolos é uma lista de pares (identificador, localização) 
    e representa um mapeamento entre variáveis e posições na memória *)
type symbols = (string * location) list;;
```

em [nossa implementação de ] $L_2$, a memória é feita em dois passos:

1. identificadores são armazenados em uma *tabela de símbolos*, que associa identificadores a localizações na memória;

2. a memória é uma associação entre localizações e valores.

tanto a tabela de símbolos quanto a memória são listas: `symbols` é uma lista de pares `string * location` e `memory` é uma lista de pares `location * value`.

métodos sobre `symbols`:

```ocaml
(** verifica se a variável `x` está na tabela de símbolos `table` *)
let rec is_bound (x: string) (table: symbols) : bool = match table with
    | [] -> false
    | (y, l) :: table -> if x = y then true else is_bound x table
;;

(** retorna a localização da variável `x` na tabela de símbolos `table` *)
let rec search (x: string) (table: symbols) : location option = match table with
    | [] -> None
    | (y, l) :: table -> if x = y then Some l else search x table
;;

(** adiciona uma nova variável `x` na tabela de símbolos `table` *)
let rec extend (x: string) (l: location) (table: symbols) : symbols = (x, l) :: table;;
```

### memória
```ocaml
(**
    uma memória é uma lista de pares (localização, valor) e representa um mapeamento entre localizações e valores *)
type memory = (location * value) list;;

let rec exists (loc: location) (mem: memory) : bool = match mem with
    | [] -> false
    | (l, v) :: mem -> if loc = l then true else exists loc mem
;;

let rec get (loc: location) (mem: memory) : value option = match mem with
    | [] -> None
    | (l, v) :: mem -> if loc = l then Some v else get loc mem
;;

(** atualiza um local na memória e reordena a memória de acordo com a localização (fst mem) *)
let rec set (loc: location) (v: value) (mem: memory) : memory = (
    let rec aux acc = function
        | [] -> List.rev ((loc, v) :: acc)
        | (l, vv) :: tail ->
            if l = loc then List.rev_append acc ((loc, v) :: tail)
            else aux ((l, vv) :: acc) tail
    in
    aux [] mem
)

(** ordena a memória em função das localizações (loc, fst mem) *)
let sort (mem: memory) : memory =
    let compare (l1, _) (l2, _) = compare l1 l2 in
    List.sort compare mem
;;

(** retorna a próxima posição livre na memória *)
let where mem =
    mem
    |> List.map fst
    |> List.sort compare
    |> List.fold_left (fun expect l ->
            if l = expect then expect + 1 else expect
        ) 0
```


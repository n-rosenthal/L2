(**
    `src/Constructions.ml`
    
    Estruturas usadas para a inferência estática de tipos (ambiente de tipos)
    e para a avaliação de termos (memória e tabela de símbolos).
  *)

open Types
open Terms




(** ambiente de tipos: (string * tipo) list *)
type ambiente = (string * tipo) list;;

(** dado um identificador `x` e um ambiente `env`,
    retorna o tipo de `x` em `env`, se `x` estiver em `env`. *)
let rec lookup (x: string) (env: ambiente) : tipo option = match env with
    | [] -> None
    | (y, t) :: env -> if x = y then Some t else lookup x env
;;


(** dado um identificador `x`, um tipo `t` e um ambiente `env`,
    adiciona/atualiza (x,t) no ambiente, preservando outras entradas. *)
let rec put (x: string) (t: tipo) (env: ambiente) : ambiente =
        match env with
        | [] -> [(x, t)]
        | (y, ty) :: env' ->
            if x = y then
              (* atualiza a primeira ocorrência *)
                (x, t) :: env'
            else
              (* preserva a cabeça e continua procurando *)
                (y, ty) :: put x t env'
;;



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


(**
    Tabela de Símbolos e Memória para Avaliação

    O usuário/programador de L_2 tem acesso a variáveis (Identifier x).
    Ele pode:
        (1) definir uma nova variável, usando o comando `let x = e1 in e2`
        (2) obter o valor de uma variável, usando, como comando, o nome daquela variável (`x`)
            este nome é, na árvore sintática, um Identifier x.

            Precisamos, então, de um mapeamento entre variáveis e os valores que elas apontam.
            Em L_2, entretanto, a avaliação de uma variável não produz seu valor;
            Ao invés disso, em L_2, a avaliação de uma variável produz uma localização na memória:

            (Identifier x) -> (Location l)

    O usuário/programador de L_2 NÃO tem acesso a posições na memória. Isto é feito em tempo de avaliação,
    pelo avaliador/interpretador/compilador.
    As operações sobre posições na memória são todas feitas NA FUNÇÃO `step`.

    O valor apontado por uma variável é obtido através da avaliação de uma expressão (Dereference (Identifier x)),
    da seguinte forma:

            (Dereference (Identifier x)) -> (Dereference (Location l)) -> (Value v)
    
    que é equivalente a

            !x -> !l -> v

    ou seja, avaliamos uma variável para sua localização na memória. a operação de dereferência (!) retorna o valor apontado por uma localização na memória.


    É por isso que PRECISAMOS DE DUAS CONSTRUÇÕES:
        uma TÁBELA DE SÍMBOLOS, que mapeia IDENTIFICADORES/VARIÁVEIS para LOCALIZAÇÕES/POSIÇÕES NA MEMÓRIA;
        uma MEMÓRIA, que mapeia LOCALIZAÇÕES/POSIÇÕES para VALORES.
    
    apesar de mais custosa, talvez essa abordagem se assemelhe mais a implementação real de uma linguagem de programação. (?)


    a tabela de símbolos é apenas uma lista de pares (identificador: string, localização: int) e é usada através de seus métodos:
        `is_bound`          - verifica se a variável `x` está na tabela de símbolos `table`;
        `search`            - retorna a localização da variável `x` na tabela de símbolos `table`;
        `extend`            - adiciona uma nova variável `x` na tabela de símbolos `table`;

    a memória, por sua vez, é uma lista de pares (localização: int, valor: value) e é usada através de seus métodos:
        `set`               - atualiza um local na memória;
        `get`               - retorna o valor de um local na memória;
        `new`               - cria uma nova localização na memória;
    
    a função `loc_of_identifier` é o meio-campo entre as duas estruturas; dada uma variável `x`, que está na tabela de símbolos,
    recuperamos sua localização `loc` na memória.
**)

(** localização na memória, aliás int *)
type location = int;;

(** uma tabela de símbolos é uma lista de pares (identificador, localização) 
    e representa um mapeamento entre variáveis e posições na memória *)
type symbols = (string * location) list;;

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
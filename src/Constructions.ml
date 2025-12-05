(**
    `src/Constructions.ml`
    
    Estruturas usadas para a inferência estática de tipos (ambiente de tipos)
    e para a avaliação de termos (memória)
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
    Memória para avaliação de termos
**)
type memory = (location * string * value) list
and location = int;;

let rec set (mem: memory) (loc: location) (v: value) : memory =
    match mem with
    | [] -> [(loc, "", v)]
    | (l, s, v) :: mem -> if l = loc then (loc, s, v) :: mem else (l, s, v) :: set mem loc v
;;

let rec get (mem: memory) (loc: location) : (location * string * value) option = match mem with
    | [] -> None
    | (l, s, v) :: mem -> if l = loc then Some (l, s, v) else get mem loc
;;


let rec loc_of_identifier (mem: memory) (x: string) : location option = match mem with
    | [] -> None
    | (l, s, v) :: mem -> if s = x then Some l else loc_of_identifier mem x
;;

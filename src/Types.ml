(**
    `src/Types.ml`
    
    Definição do sistema de tipos para a linguagem `L_2`

    `ErrorType` não é um tipo na linguagem `L_2`. Ao invés disso,
    este tipo representa a ocorrência de um erro durante a inferência
    estática de tipos. O programador de `L_2` não deve ter acesso a
    `ErrorType`.
*)


(** sistema de tipos para a linguagem `L_2` *)
type  tipo  =
    | Unit                      (* unit *)
    | Int                       (* número inteiro *)
    | Bool                      (* booleano *)
    | Reference of tipo         (* referência de tipos *)
    | ErrorType of string       (* erro de tipagem *)
;;


(** verifica se `t1` e `t2` são tipos equivalentes *)
let rec eq_tipo (t1: tipo) (t2: tipo) : bool = match t1, t2 with
    | Unit, Unit | Int, Int | Bool, Bool -> true
    | Reference t1, Reference t2 -> eq_tipo t1 t2
    | _ -> false
;;


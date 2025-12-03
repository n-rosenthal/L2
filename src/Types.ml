(**
  `src/Types.ml`
  
  Definição do sistema de tipos para a linguagem `L2`
*)

(** Sistema de tipos de L2 *)
type tipo   = ..;;

(** O sistema de tipos é declarado extensível pois, em `typeinfer.ml`,
será definido o tipo-erro para a inferência de tipos.*)
type  tipo  +=
    | Unit                    (* unit *)
    | Int                     (* número inteiro *)
    | Bool                    (* booleano *)
    | Reference of tipo       (* referência de tipos *)
;;

let rec eq_tipo (t1: tipo) (t2: tipo) : bool = match t1, t2 with
    | Unit, Unit | Int, Int | Bool, Bool -> true
    | Reference t1, Reference t2 -> eq_tipo t1 t2
    | _ -> false
;;

(**
    A inferência estática de tipos extende o sistema de tipos de `L2`
    para incluir um tipo erro, `ErrorType`. Isso garante a totalidade
    ou completude trivial do algoritmo: para todo termo `e`, `typeinfer e`
    retornará um tipo. Isto é diferente do que dizer que se `e` é tipável,
    então `typeinfer e` será capaz de derivar o tipo de `e`.

    `ErrorType` não deve ser um tipo acessível ao programador.
**)
type tipo += 
    | ErrorType of string;;

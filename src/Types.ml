(**
  `src/Types.ml`
  
  Definição do sistema de tipos para a linguagem `L2`
*)

(** Sistema de tipos de L2 *)
type  tipo =
    | Unit                    (* unit *)
    | Int                     (* número inteiro *)
    | Bool                    (* booleano *)
    (**
    | Ref of tipo             (* tipo referência *)
    | Arrow of tipo * tipo    (* tipo função *)
    | Product of tipo * tipo  (* tipo produto *)
    *)
;;

(** repr. string de um tipo *)
let rec string_of_tipo t =
    match t with
    | Unit -> "unit"
    | Int -> "int"
    | Bool -> "bool"
    (**
    | Ref t -> "ref " ^ string_of_tipo t
    | Arrow (t1, t2) -> string_of_tipo t1 ^ " -> " ^ string_of_tipo t2
    | Product (t1, t2) -> string_of_tipo t1 ^ " * " ^ string_of_tipo t2
    *)
;;
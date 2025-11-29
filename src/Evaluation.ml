(**
  `src/Evaluation.ml`
  
  Avaliação de termos para a linguagem `L2`
*)


open Types
open Terms

open TypeInference

exception RuntimeError of string * term;;

let is_value (e: term) : bool = match e with
    | Integer _ -> true
    | Boolean _ -> true
    | Unit      -> true
    | _         -> false
and is_bool (e: term) : bool = match e with
    | Boolean b -> true
    | _         -> false
and value_of_term (e: term) : value option = match e with
    | Integer n -> Some (VInteger n)
    | Boolean b -> Some (VBoolean b)
    | Unit      -> Some (VUnit)
    | _         -> None
and term_of_value (v: value) : term option = match v with
    | VInteger n -> Some (Integer n)
    | VBoolean b -> Some (Boolean b)
    | VUnit      -> Some (Unit)
    | _          -> None
;;


(** memória: (location * identifier * value) list *)
type memory = (int * string * value) list;;

(** dada uma memória `mem` e um identificador `x`,
    retorna o valor associado ao identificador `x`, se houver. *)
let rec lookup (x: string) (mem: memory) : value option = match mem with
    | [] -> None
    | (l, y, v) :: mem -> if x = y then Some v else lookup x mem
;;

(** dada uma memória de triplas 1-indexada (l, _, _)
    ordena as triplas em ordem crescente de `l`. 
*)
let rec sort (mem: memory) : memory = match mem with
    | [] -> []
    | (l, x, v) :: mem -> (l, x, v) :: sort (List.filter (fun (l', _, _) -> l' > l) mem)
;;

(** dada uma memória `mem`, um identificador `x` e um valor `v`,
    atualiza a tripla `(l, x, v)` na memória `mem`, se `x` estiver em `mem`,
    ou adiciona uma nova tripla com uma nova localização. *)
let put (x: string) (v: value) (mem: memory) : memory =
    (* tenta atualizar *)
    let rec update mem =
        match mem with
            | [] -> None
            | (l, y, vy) :: mem' ->
                if x = y then
                    Some ((l, x, v) :: mem')
                else
                    match update mem' with
                    | Some mem'' -> Some ((l, y, vy) :: mem'')
                    | None -> None
    in
        match update mem with
        | Some mem_updated ->
            mem_updated
        | None ->
            (* não existia: aloca nova localização *)
            let next_loc =
                List.fold_left (fun acc (l,_,_) -> max acc l) 0 mem + 1
            in
            (next_loc, x, v) :: mem
let string_of_mem (mem: memory) : string = 
    let rec string_of_mem' (mem: memory) : string = match mem with
        | [] -> ""
        | (l, x, v) :: mem -> "(" ^ string_of_int l ^ ", " ^ x ^ ", " ^ string_of_value v ^ ") " ^ string_of_mem' mem
    in "[" ^ string_of_mem' (sort mem) ^ "]"
;;

(** faz um passo, se possível, na avaliação de um termo `e` sobre uma memória `mem` em L2. *)
let rec step (e: term) (mem: memory) : (term * memory) option = match e with
    (** n, número inteiro *)
    | Integer n -> Some (Integer n, mem)
    
    (** b, booleano *)
    | Boolean b -> Some (Boolean b, mem)

    (** x, identificador *)
    | Identifier x -> (match lookup x mem with
        (** se `x` estiver em `mem`, retorne `Some (v, mem)` com `v` o valor associado a `x` *)
        | Some v -> (match term_of_value v with
            | Some t -> Some (t, mem)
            | None -> None)

        (** senão, retorne `None` *)
        | None -> None
    )

    (** if e1 then e2 else e3, operador condicional *)
    | Conditional (e1, e2, e3) -> (
        (** e1 -> e1' => if(e1, e2, e3) -> if(e1', e2, e3) *)
        if not (is_value e1) then (
            match step e1 mem with
            | Some (e1', mem') -> Some (Conditional (e1', e2, e3), mem')
            | None -> None
        ) else (match (typeinfer e1 []) with
            (** v1: Bool *)
            | Bool -> (
                (** v1: Bool = true => if(e1, e2, e3) -> e2 *)
                if (e1 = Boolean true) then Some (e2, mem)

                (** v1: Bool = false => if(e1, e2, e3) -> e3 *)                        
                else Some (e3, mem)
            )

            (** v1 !: Bool*)
            | _ -> None
        )
    )

    (** op. binárias *)
    | BinaryOperation (op, e1, e2) -> (
        (** e1 -> e1' => op(e1, e2) -> op(e1', e2) *)
        if not (is_value e1) then
            (match step e1 mem with
                | Some (e1', mem') -> Some (BinaryOperation (op, e1', e2), mem')
                | None -> None)
            
        (** v1, e2 -> e2' => op(v1, e2) -> op(v1, e2') *)
        else if (is_value e1 && not (is_value e2)) then (
            match step e2 mem with
            | Some (e2', mem') -> Some (BinaryOperation (op, e1, e2'), mem')
            | None -> None
        
        (** redundante, confirmatório *)
        (** v1, v2 => op(v1, v2) -> v *)
        ) else (match (value_of_term e1, value_of_term e2) with
            | (Some v1, Some v2) -> (match (op, v1, v2) with
                (** op. binárias aritméticas *)
                | (Add, VInteger n1, VInteger n2) -> Some (Integer (n1 + n2), mem)
                | (Sub, VInteger n1, VInteger n2) -> Some (Integer (n1 - n2), mem)
                | (Mul, VInteger n1, VInteger n2) -> Some (Integer (n1 * n2), mem)
                | (Div, VInteger n1, VInteger n2) -> if n2 = 0 then None else Some (Integer (n1 / n2), mem)

                (** op. binárias aritméticas relacionais *)
                | (Eq, VInteger n1, VInteger n2) -> Some (Boolean (n1 = n2), mem)
                | (Neq, VInteger n1, VInteger n2) -> Some (Boolean (n1 <> n2), mem)
                | (Lt, VInteger n1, VInteger n2) -> Some (Boolean (n1 < n2), mem)
                | (Leq, VInteger n1, VInteger n2) -> Some (Boolean (n1 <= n2), mem)
                | (Gt, VInteger n1, VInteger n2) -> Some (Boolean (n1 > n2), mem)
                | (Geq, VInteger n1, VInteger n2) -> Some (Boolean (n1 >= n2), mem)

                (** op. binárias lógicas *)
                | (And, VBoolean b1, VBoolean b2) -> Some (Boolean (b1 && b2), mem)
                | (Or, VBoolean b1, VBoolean b2) -> Some (Boolean (b1 || b2), mem)

                (** erro *)
                | _ -> None)

            (** erro *)
            | _ -> None
        )
    )
    
        (** while e1 do e2 *)
        | While (e1, e2) -> (
            (** e1 -> e1' => while(e1, e2) -> while(e1', e2) *)
            if not (is_value e1) then (
                match step e1 mem with
                | Some (e1', mem') -> Some (While (e1', e2), mem')
                | None -> None
            ) else (
                (* e1 é valor: deve ser Boolean true/false *)
                match e1 with
                | Boolean true ->
                    (* while true do e2 -> e2; while e1 do e2  (re-evalua a condição depois de e2) *)
                    Some (Sequence (e2, While (e1, e2)), mem)
                | Boolean false ->
                    (* while false do e2 -> unit *)
                    Some (Unit, mem)
                | _ ->
                    (* condição não-booleano *)
                    None
            )
        )
    
        (** x := e1 *)
        | Assignment (x, e1) -> (
            if not (is_value e1) then (
                match step e1 mem with
                | Some (e1', mem') -> Some (Assignment (x, e1'), mem')
                | None -> None
            ) else (
                match x with
                | Identifier name -> (
                    match value_of_term e1 with
                    | Some v ->
                        let mem' = put name v mem in
                        Some (Unit, mem')
                    | None ->
                        None
                )
                | _ ->
                    None
            )
        )
    
        (** let x: t = e1 in e2 *)
        | Let (x, t, e1, e2) -> (
            (** e1 -> e1' => let x: t = e1 in e2 -> let x: t = e1' in e2 *)
            if not (is_value e1) then (
                match step e1 mem with
                | Some (e1', mem') -> Some (Let (x, t, e1', e2), mem')
                | None -> None
            ) else (
                match value_of_term e1 with
                | Some v ->
                    let mem' = put x v mem in
                    Some (e2, mem')
                | None -> None
            )
        )
    
        (** new e1 *)
        | New e1 -> (
            if not (is_value e1) then (
                match step e1 mem with
                | Some (e1', mem') -> Some (New e1', mem')
                | None -> None
            ) else (
                match value_of_term e1 with
                | Some v ->
                    let next_loc =
                        List.fold_left (fun acc (l,_,_) -> max acc l) 0 mem + 1
                    in
                    let loc_name = "loc_" ^ string_of_int next_loc in
                    let mem' = (next_loc, loc_name, v) :: mem in
                    Some (Identifier loc_name, mem')
                | None -> None
            )
        )
    
        (** !e1 *)
        | Derefence e1 -> (
            if not (is_value e1) then
                match step e1 mem with
                | Some (e1', mem') -> Some (Derefence e1', mem')
                | None -> None
            else
                match e1 with
                | Identifier name -> (
                    match lookup name mem with
                    | Some v -> (
                        match term_of_value v with
                        | Some t -> Some (t, mem)
                        | None -> None
                    )
                    | None -> None
                )
                | _ -> None
        )
        
    

    (** () *)
    | Unit -> Some (Unit, mem)
    | Sequence (e1, e2) -> (
        (** e1 -> e1' => e1; e2 -> e1'; e2 *)
        if not (is_value e1) then (
            match step e1 mem with
            | Some (e1', mem') -> Some (Sequence (e1', e2), mem')
            | None -> None
        ) else (
            (* e1 é valor; deve ser Unit para prosseguir *)
            match e1 with
            | Unit -> Some (e2, mem)
            | _ -> None
        )
    )

    | _ -> failwith "NotImplemented"
;;

(** operador ->* sobre um termo `e` em L2. *)
let rec step_star (e: term) (mem: memory) : (term * memory) option = match step e mem with
    | Some (e', mem') when not (is_value e') -> step_star e' mem'
    | Some (e', mem') -> Some (e', mem')
    | None -> Some (e, mem)
;;

(** operador ->* imperativo *)
let stepn (e: term) (n: int) : (term * memory) =
    let rec stepn' (e: term) (n: int) (mem: memory) : (term * memory) = match n with
        | 0 -> (e, mem)
        | _ -> (match step e mem with
            | Some (e', mem') -> stepn' e' (n - 1) mem'
            | None -> (e, mem))
    in stepn' e n []
;;

let evaluate (e: term) (mem: memory) : (value * memory) option = match step_star e mem with
    | Some (e', mem') -> (match value_of_term e' with
        | Some v -> Some (v, mem')
        | None -> None)
    | None -> None
;;


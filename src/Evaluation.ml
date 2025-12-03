(**
  `src/Evaluation.ml`
  DEFINE as funções de AVALIAÇÃO de termos para linguagem L2.

  Avaliação de termos para a linguagem `L2`.
*)


open Types                  (*  tipos da linguagem `L2` *)
open Terms                  (*  sintaxe de termos sobre `L2` *)
open Constructions          (*  memória de valores, regras de avaliação de termos *)
open Representations        (*  repr. string para termos, valores, tipos, ambientes de tipos e memória *)
open TypeInference          (*  inferência estática de tipos para `L2` *)


(** ---
    Predicados para avaliação small-step e conversão entre formas
    --- 
*)

(** verifica se um termo representa um valor *)
let is_value_term = function
    | Integer _ | Boolean _ | Unit | Location _ -> true
    | _ -> false

(** converte um termo para um valor *)
let value_of_term = function
    | Integer n -> Some (VInteger n)
    | Boolean b -> Some (VBoolean b)
    | Unit      -> Some VUnit
    | Location l ->
        (* location is a value but its runtime value is found in memory *)
        None
    | _ -> None

(** converte um valor para um termo *)
let term_of_value = function
    | VInteger n -> Some (Integer n)
    | VBoolean b -> Some (Boolean b)
    | VUnit      -> Some Unit
    | _ -> None

(** ---
    helpers para as regras de avaliação de um termo
    ---
*)
let make_rule name req ens =
    { name; requires = req; ensures = ens }

let rule_from_mem mem e name req ens =
    make_rule name (string_of_mem mem ^ " ⊢ " ^ req) (string_of_mem mem ^ " ⊢ " ^ ens)

(** ---
    helpers para gerenciamento da memória
    ---
*)
let fresh_loc (mem : memory) : location =
    match mem with
    | [] -> 0
    | (l, _, _) :: rest ->
        (* compute max loc *)
        let max_l = List.fold_left (fun acc (l, _, _) -> if l > acc then l else acc) l rest in
        max_l + 1

let mem_set (mem : memory) (loc : location) (name : string) (v : value) : memory =
    let rec aux acc = function
        | [] -> List.rev ((loc, name, v) :: acc)
        | (l, s, vv) :: tail ->
            if l = loc then List.rev_append acc ((loc, name, v) :: tail)
            else aux ((l, s, vv) :: acc) tail
    in
    aux [] mem

(** ---
    aplicação de operações bináras sobre valores
    ---
*)

(** dados dois valores `v` e `u`, e uma operador binário `bop`,
    tenta aplicar `(bop v u)` e retornar seu resultado;
    se não for possível, um termo `RuntimeError s` será retornado *)
let apply_binop bop v1 v2 =
        match (bop, v1, v2) with
        | (Add, VInteger a, VInteger b) -> VInteger (a + b)
        | (Sub, VInteger a, VInteger b) -> VInteger (a - b)
        | (Mul, VInteger a, VInteger b) -> VInteger (a * b)
        | (Div, VInteger _, VInteger 0) -> EvaluationError "Divisão por zero"
        | (Div, VInteger a, VInteger b) -> VInteger (a / b)

        | (Eq, VInteger a, VInteger b)  -> VBoolean (a = b)
        | (Neq, VInteger a, VInteger b) -> VBoolean (a <> b)
        | (Lt, VInteger a, VInteger b)  -> VBoolean (a < b)
        | (Leq, VInteger a, VInteger b) -> VBoolean (a <= b)
        | (Gt, VInteger a, VInteger b)  -> VBoolean (a > b)
        | (Geq, VInteger a, VInteger b) -> VBoolean (a >= b)

        | (Eq, VBoolean a, VBoolean b)  -> VBoolean (a = b)
        | (Neq, VBoolean a, VBoolean b) -> VBoolean (a <> b)

        | (And, VBoolean a, VBoolean b) -> VBoolean (a && b)
        | (Or,  VBoolean a, VBoolean b) -> VBoolean (a || b)

        | _ -> EvaluationError ("Erro de tipo para o operador binário " ^ (string_of_binary_operator bop) ^
                                " sobre os termos " ^ (string_of_value v1) ^ " e " ^ (string_of_value v2))
;;

(** substitui um termo `x` por um valor `y` em um termo `e`
    Implementação para expressões Let (x, [t], e1, e2) = (x, [t], y, e) *)
let rec substitute (x: string) (y: term) (e: term) : term =
        match e with
        | Integer _ | Boolean _ | Unit | Location _ -> e
        | Identifier s -> if s = x then y else e
        | Conditional (a, b, c) -> Conditional (substitute x y a, substitute x y b, substitute x y c)
        | BinaryOperation (op, a, b) -> BinaryOperation (op, substitute x y a, substitute x y b)
        | While (a, b) -> While (substitute x y a, substitute x y b)
        | Assignment (l, r) -> Assignment (substitute x y l, substitute x y r)
        | Let (s, t, a, b) -> if s = x then Let (s, t, substitute x y a, b) else Let (s, t, substitute x y a, substitute x y b)
        | New a -> New (substitute x y a)
        | Derefence a -> Derefence (substitute x y a)
        | Sequence (a, b) -> Sequence (substitute x y a, substitute x y b)
;;


(** ---
    Avaliação de termos
    ---
*)

(** faz um passo na avaliação de um termo, se for possível *)
let rec step    (e     :    term)
                (mem   :  memory)
                : (term * memory * eval_rule, string) result =
    match e with
            (* values are stuck (no step) *)
            | Integer _ | Boolean _ | Unit | Location _ ->
                Error ("term is a value; no step")
          
            (* Identifier: fetch the value bound to the identifier in memory.
               If present, replace identifier by the term-of-value.
               If the identifier is not bound -> runtime error (stuck). *)
            | Identifier x ->
                (match loc_of_identifier mem x with
                 | None ->
                     let msg = "unbound identifier '" ^ x ^ "' in memory" in
                     let r = rule_from_mem mem e "E-VarError" ("'" ^ x ^ "'") msg in
                     Error msg
                 | Some loc ->
                     (match get mem loc with
                      | None ->
                          let msg = "invalid location for identifier '" ^ x ^ "'" in
                          Error msg
                      | Some (_, _, v) ->
                          (match term_of_value v with
                           | Some t' ->
                               let r = rule_from_mem mem e "E-Var" ("'" ^ x ^ "'") ("-> " ^ ast_of_term t') in
                               Ok (t', mem, r)
                           | None ->
                               (* value has no term representation (EvaluationError) -> stuck *)
                               let msg = "identifier '" ^ x ^ "' maps to an evaluation error" in
                               Error msg)))
          
            (* Binary operation small-step *)
            | BinaryOperation (op, e1, e2) ->
                if not (is_value_term e1) then
                  (* step e1 *)
                  (match step e1 mem with
                   | Error s -> Error s
                   | Ok (e1', mem', r) -> Ok (BinaryOperation (op, e1', e2), mem', r))
                else if not (is_value_term e2) then
                  (* step e2 *)
                  (match step e2 mem with
                   | Error s -> Error s
                   | Ok (e2', mem', r) -> Ok (BinaryOperation (op, e1, e2'), mem', r))
                else
                  (* both are values: apply operator *)
                  (match (value_of_term e1, value_of_term e2) with
                   | (Some v1, Some v2) ->
                       let resv = apply_binop op v1 v2 in
                       (match term_of_value resv with
                        | Some tres ->
                            let r = rule_from_mem mem e ("E-BinOp " ^ string_of_binary_operator op)
                                      (ast_of_term e) (ast_of_term tres) in
                            Ok (tres, mem, r)
                        | None ->
                            (* runtime error value returned (EvaluationError) *)
                            let msg = (match resv with EvaluationError s -> s | _ -> "unknown runtime error") in
                            Error msg)
                   | _ -> Error "binary operation on non-concrete values")
          
            (* Conditional: small-step left-to-right *)
            | Conditional (c, e_true, e_false) ->
                if not (is_value_term c) then
                  (match step c mem with
                   | Error s -> Error s
                   | Ok (c', mem', r) -> Ok (Conditional (c', e_true, e_false), mem', r))
                else
                  (* condition is a value *)
                  (match value_of_term c with
                   | Some (VBoolean true) ->
                       let r = rule_from_mem mem e "E-IfTrue" (ast_of_term c) (ast_of_term e_true) in
                       Ok (e_true, mem, r)
                   | Some (VBoolean false) ->
                       let r = rule_from_mem mem e "E-IfFalse" (ast_of_term c) (ast_of_term e_false) in
                       Ok (e_false, mem, r)
                   | _ ->
                       Error "condition of if is not a boolean")
          
            (* While -> expands to conditional with recursion (small-step encoding) *)
            | While (cond, body) ->
                let expanded = Conditional (cond, Sequence (body, While (cond, body)), Unit) in
                let r = rule_from_mem mem e "E-While" (ast_of_term e) (ast_of_term expanded) in
                Ok (expanded, mem, r)
          
            (* Assignment: step left, right; when lhs identifies a location update memory and become Unit *)
            | Assignment (lhs, rhs) ->
                (* step lhs until it is Location or Identifier *)
                (match lhs with
                 | Identifier x ->
                     if not (is_value_term rhs) then
                       (* step rhs first (right-to-left or left-to-right choice; here evaluate rhs) *)
                       (match step rhs mem with
                        | Error s -> Error s
                        | Ok (rhs', mem', r) -> Ok (Assignment (lhs, rhs'), mem', r))
                     else
                       (* rhs is value: update memory if x bound *)
                       (match loc_of_identifier mem x with
                        | None -> Error ("assignment: unbound identifier '" ^ x ^ "'")
                        | Some loc ->
                            (match value_of_term rhs with
                             | Some vv ->
                                 let mem' = mem_set mem loc x vv in
                                 let r = rule_from_mem mem e "E-Assign" (ast_of_term e) ("unit") in
                                 Ok (Unit, mem', r)
                             | None -> Error "assignment rhs is not a value"))
                 | Location l ->
                     if not (is_value_term rhs) then
                       (match step rhs mem with
                        | Error s -> Error s
                        | Ok (rhs', mem', r) -> Ok (Assignment (lhs, rhs'), mem', r))
                     else
                       (match value_of_term rhs with
                        | Some vv ->
                            let mem' = mem_set mem l "" vv in
                            let r = rule_from_mem mem e "E-AssignLoc" (ast_of_term e) ("unit") in
                            Ok (Unit, mem', r)
                        | None -> Error "assignment rhs is not a value")
                 | _ ->
                     (* step lhs *)
                     (match step lhs mem with
                      | Error s -> Error s
                      | Ok (lhs', mem', r) -> Ok (Assignment (lhs', rhs), mem', r)))
          
            (* Let: evaluate e1 until value then substitute *)
            | Let (x, _t, e1, e2) ->
                if not (is_value_term e1) then
                  (match step e1 mem with
                   | Error s -> Error s
                   | Ok (e1', mem', r) -> Ok (Let (x, _t, e1', e2), mem', r))
                else
                  (* do syntactic substitution *)
                  let e2' = substitute x e1 e2 in
                  let r = rule_from_mem mem e "E-Let" (ast_of_term e1) (ast_of_term e2') in
                  Ok (e2', mem, r)
          
            (* New: allocate a fresh location when inner is a value *)
            | New e1 ->
                if not (is_value_term e1) then
                  (match step e1 mem with
                   | Error s -> Error s
                   | Ok (e1', mem', r) -> Ok (New e1', mem', r))
                else
                  (match value_of_term e1 with
                   | Some v ->
                       let loc = fresh_loc mem in
                       let mem' = (loc, "", v) :: mem in
                       let r = rule_from_mem mem e "E-New" (ast_of_term e1) ("Location " ^ string_of_int loc) in
                       Ok (Location loc, mem', r)
                   | None -> Error "new: inner is not a storable value")
          
            (* Derefence: !e -> if e reduces to Location l, replace by term_of_value(v) *)
            | Derefence e1 ->
                if not (is_value_term e1) then
                  (match step e1 mem with
                   | Error s -> Error s
                   | Ok (e1', mem', r) -> Ok (Derefence e1', mem', r))
                else
                  (match e1 with
                   | Location l ->
                       (match get mem l with
                        | None -> Error ("deref: invalid location " ^ string_of_int l)
                        | Some (_, _, v) ->
                            (match term_of_value v with
                             | Some t' ->
                                 let r = rule_from_mem mem e "E-Deref" (ast_of_term e1) (ast_of_term t') in
                                 Ok (t', mem, r)
                             | None ->
                                 Error "deref: stored value has no term representation"))
                   | _ -> Error "deref: inner is not a location")
          
            (* Sequence: e1; e2 -> if e1 not value step it; if e1 value then result is e2 *)
            | Sequence (e1, e2) ->
                if not (is_value_term e1) then
                  (match step e1 mem with
                   | Error s -> Error s
                   | Ok (e1', mem', r) -> Ok (Sequence (e1', e2), mem', r))
                else
                  let r = rule_from_mem mem e "E-Seq" (ast_of_term e1) (ast_of_term e2) in
                  Ok (e2, mem, r)
          
            (* Location as term should be a value and is handled earlier *)
            | Location _ -> Error "location is a value; no step"
          
            (* Fallback: unknown term form *)
            | _ -> Error ("no small-step rule for term: " ^ ast_of_term e)
          
          (* ------------------------------------------------------------ *)
          (* multi_step : run steps until a value or stuck. Returns the final
             term, final memory and the accumulated rules in the order they happened. *)
          (* ------------------------------------------------------------ *)
          
          let rec multi_step (e : term) (mem : memory) (limit : int) : (term * memory * evaluation, string) result =
            if limit <= 0 then Error "step limit reached"
            else if is_value_term e then Ok (e, mem, [])
            else
              match step e mem with
              | Error s -> Error s
              | Ok (e', mem', r) ->
                  (match multi_step e' mem' (limit - 1) with
                   | Error s -> Error s
                   | Ok (final_t, final_mem, trace) -> Ok (final_t, final_mem, (r :: trace)))
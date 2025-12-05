
          
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


        (** operações binárias:
            avaliação da esquerda para a direita:

            se o primeiro termo (e1) não for um valor, avalie-o até que seja
            se o segundo termo (e2) não for um valor, avalie-o até que seja 
            quando ambos termos forem valores, tente fazer a operação binária *)
        | BinaryOperation (op, e1, e2) ->
            (** se `e1` não for um valor, isto é, se for possível dar um passo e1 -> e1', então tente dar um passo. *)
            if not (is_value_term e1) then
                (match step e1 mem with
                    (** e1 !-> e1', erro. *)
                    | Error s -> Error s

                    (** e1 -> e1' => e1 op e2 -> e1' op e2. *)
                    | Ok (e1', mem', r) -> 
                        Ok (BinaryOperation (op, e1', e2),
                            mem',
                            {name   = "E-BinOp" ^ string_of_binary_operator op ^ " 1";
                            pre     = ast_of_term e1 ^ ", " ^ string_of_mem ^ mem ^ " -> " ^ ast_of_term e1' ^ ", " ^ string_of_mem ^ mem';
                            post    = ast_of_term e ^ ", " ^ string_of_mem ^ mem ^ " -> " ^ ast_of_term (BinaryOperation (op, e1', e2)) ^ ", " ^ string_of_mem ^ mem'} :: r))
            (** se `e1` = `v1` for um valor, mas `e2` não for um valor, então tente dar um passo e2 -> e2'. *)
            else if not (is_value_term e2) then
                (match step e2 mem with
                    (** e2 !-> e2', erro. *)
                    | Error s -> Error s

                    (** e2 -> e2' => e1 op e2 -> e1 op e2'. *)
                    | Ok (e2', mem', r) -> 
                        Ok (BinaryOperation (op, e1, e2'),
                            mem',
                            {name   = "E-Binop" ^ string_of_binary_operator op ^ " 2";
                            pre     = ast_of_term e2 ^ ", " ^ string_of_mem ^ mem ^ " -> " ^ ast_of_term e2' ^ ", " ^ string_of_mem ^ mem';
                            post    = ast_of_term e ^ ", " ^ string_of_mem ^ mem ^ " -> " ^ ast_of_term (BinaryOperation (op, e1, e2')) ^ ", " ^ string_of_mem ^ mem'} :: r))

            (** são valores `e1` = `v1` e `e2` = `v2`. *)
            else (match (value_of_term e1, value_of_term e2) with
                    | (Some v1, Some v2) ->
                        (** aplique a função para computar o resultado de uma operação binária. *)
                        let result_value = apply_binop op v1 v2 in

                        (** se `result_value` for um valor, então retorne-o. *)
                        (match term_of_value result_value with
                            | Some real_value -> 
                                Ok (real_value,
                                    mem,
                                    {name = "E-Binop" ^ string_of_binary_operator op;
                                    pre   = string_of_value rv ^ " = " ^ ast_of_term e1 ^ " " ^ string_of_binary_operator op ^ " " ^ ast_of_term e2;
                                    post  = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term real_value ^ ", " ^ string_of_mem mem} :: r)

                            | None ->
                                    (* runtime error value returned (EvaluationError) *)
                                    let msg = (match result_value with EvaluationError s -> s | _ -> "erro de avaliação desconhecido ao longo da avaliação de uma operação binária: " ^ string_of_value result_value) in
                                    Error msg)
                        | _ -> Error "Operação binária sobre termos que não podem ser avaliados")


            (** if(e1, e2, e3) Conditional
                avaliação da esquerda para direita:

                se e1 não for um valor, avalie-o até que seja;
                se e1 for verdadeiro, então retorne e2;
                se e1 for falso     , então retorne e3
                [se e1 for um valor não booleano, erro]
                *)
            | Conditional (e1, e2, e3) ->
                (** e1 -> e1' => if(e1, e2, e3) -> if(e1', e2, e3) *)
                if not (is_value_term e1) then
                    (match step e1 mem with
                    (** e1 !-> e1' => erro *)
                    | Error s -> Error s
                    
                    (** e1 -> e1' => if(e1, e2, e3) -> if(e1', e2, e3) *)
                    | Ok (e1', mem', r) -> 
                        Ok  (Conditional (e1', e2, e3), 
                            mem', 
                            {name   = "E-If 3";
                            pre     =   ast_of_term ^ e1 ", " ^ string_of_mem ^ mem " -> " ^
                                        ast_of_term ^ e1' ", " ^ string_of_mem ^ mem';
                            post    =   ast_of_term ^ e ^ ", " ^ string_of_mem ^ mem ^ " -> " ^
                                        ast_of_term ^ Conditional (e1', e2, e3) ^  ", " ^ string_of_mem ^ mem'} :: r))
                else
                    (* `e1` = `v1` é um valor *)
                    (match value_of_term c with
                        (** se `v1` for verdadeiro, então retorne `e2`. *)
                        | Some (VBoolean true) -> (e2, mem, {
                            name    = "E-If (1) True";
                            pre     = "";
                            post    = "if true then " ^ ast_of_term e2 ^ " else " ^ ast_of_term e3 ^ ", " ^ string_of_mem ^ mem ^ " -> " ^ 
                                        ast_of_term e2 ^ ", " ^ string_of_mem ^ mem} :: r)

                        (** se `v1` for falso, então retorne `e3`. *)
                        | Some (VBoolean false) -> (e3, mem, {
                            name    = "E-If (2) False";
                            pre     = "";
                            post    = "if false then " ^ ast_of_term e2 ^ " else " ^ ast_of_term e3 ^ ", " ^ string_of_mem ^ mem ^ " -> " ^ 
                                        ast_of_term e3 ^ ", " ^ string_of_mem ^ mem} :: r)

                        (** se `v1` for um valor não booleano, erro. *)
                        | _ -> Error "O termo `e1` de uma expressão `if(e1, e2, e3)` deve ser um valor booleano, mas foi " ^
                                    string_of_value (value_of_term e1))


            (** while e1 do e2
                comando while é avaliado expandindo-o para um if com e1, e2 e Unit
                 While -> expands to conditional with recursion (small-step encoding) *)
            | While (e1, e2) ->
                let expanded = Conditional (e1, Sequence (e2, While (e1, e2)), Unit) in
                Ok (expanded,
                    mem, 
                    {name   = "E-While";
                    pre     = "";
                    post    = ast_of_term e ^ ", " ^ string_of_mem ^ mem ^ " -> " ^ ast_of_term expanded ^ ", " ^ string_of_mem ^ mem } :: r)

            (* e1 := e2
                Atribuição (Assignment):
                Ordem de avaliação da esquerda para a direita
                Se `e1` não for um valor, então avalie-o até que seja;
                Se `e1` = `v1` for um valor, então decide se
                    `v1` é um identificador (variável, `Identifier x`):
                        Se `e2` não for um valor, então avalie-o até que seja;
                        Se `e2` = `v2` for um valor, então atualize `mem[x]` com `v2` e retorne Unit;
                    `v1` é um local de memória (`Location l`):
                        Se `e2` não for um valor, então avalie-o até que seja;
               Assignment: step left, right; when lhs identifies a location update memory and become Unit *)
            | Assignment (e1, e2) ->
                (match e1 with
                    (** `e1` = `x` Identifier x *)
                    | Identifier x -> (                    
                        (* se `e2` não for um valor, então avalie-o até que seja *)
                        if not (is_value_term e2) then
                            (match step rhs mem with
                            | Error s -> Error s
                            | Ok (e2', mem', r) -> 
                                Ok (Assignment (e1, e2'), 
                                    mem', 
                                    {name   = "E-Atr2";
                                    pre     = ast_of_term e2 ^ ", " ^ string_of_mem ^ mem ^ " -> " ^
                                                ast_of_term e2' ^ ", " ^ string_of_mem ^ mem';
                                    post    = ast_of_term e ^ ", " ^ string_of_mem m ^ " -> " ^
                                                ast_of_term (Assignment (e1, e2')) ^ ", " ^ string_of_mem ^ mem'} :: r))

                        else
                            (* `e2` = `v2` é um valor, então tente descobrir a posição na memória ocupada pelo Identificador x  *)
                            (match loc_of_identifier mem x with
                                (** `v2` é um identificador (variável) que não existe na memória, erro. *)
                                | None -> Error ("Atribuição: identificador '" ^ x ^ "' nao encontrado na memória " ^ string_of_mem ^ mem)

                                (** `v2` é um identificador (variável) que existe na memória, e sua posição é `loc` *)
                                | Some loc ->
                                    (** extraia o valor de `e2` *)
                                    (match value_of_term e2 with
                                    | Some vv ->
                                        (** atualize `mem[x]` com `v2` e retorne Unit *)
                                        Ok (Unit,
                                            mem',
                                            {name   = "E-Atr 1";
                                            pre     = "(Location " ^ string_of_int loc ^ ") está no domínio da memória " ^ string_of_mem ^ mem;
                                            post    = ast_of_term e ^ ", " ^ string_of_mem ^ mem ^ " -> (), " ^ string_of_mem ^ mem} :: r)
                                    | None -> Error "O lado direito (rhs, `e2`) da atribuição não é um valor")))
                
                (** `e1` = `v1` é um local de memória (`Location l`) *)
                | Location l -> (
                    (** se `e2` não for um valor, avalie-o até que seja *)
                    if not (is_value_term e2) then
                        (match step e2 mem with
                            | Error s -> Error s
                            | Ok (e2', mem', r) -> 
                                Ok (Assignment (e1, e2'), 
                                    mem', 
                                    {name   = "E-Atr2";
                                    pre     = ast_of_term e2 ^ ", " ^ string_of_mem ^ mem ^ " -> " ^
                                                ast_of_term e2' ^ ", " ^ string_of_mem ^ mem';
                                    post    = ast_of_term e ^ ", " ^ string_of_mem m ^ " -> " ^
                                                ast_of_term (Assignment (e1, e2')) ^ ", " ^ string_of_mem ^ mem'} :: r))
                    else
                        (** `e2` = `v2` é um valor, então coloque o valor `v2` atribuído ao identificador `x` na posição `loc`*)
                        (match value_of_term rhs with
                            | Some vv ->
                                let mem' = mem_set mem l "" vv in
                                Ok (Unit, 
                                    mem', 
                                    {name = } :: r)
                            | None -> Error "assignment rhs is not a value"))
                | _ ->
                     (* e1 -> e1' => e1 := e2 -> e1' := e2 *)
                    (match step e1 mem with
                        (** e1 !-> e1', erro. *)
                        | Error s -> Error s

                        (** e1 -> e1' => e1 := e2 -> e1' := e2. *)
                        | Ok (e1', mem', r) -> 
                            Ok (Assignment (e1', e2), 
                                mem', 
                                {name   = "E-Atr";
                                pre     = ast_of_term e1 ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term e1' ^ ", " ^ string_of_mem mem';
                                post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (Assignment (e1', e2)) ^ ", " ^ string_of_mem mem'} :: r)))

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
          
            (** new e 
                se `e` não for um valor, avalie-o até que seja;
                se `e` for um valor,
                    defina um novo local na memória
                    associe o valor de `e` ao local na memória
                a avaliação de `new e` produz o local da memória `l` *)
            | New e1 ->
                if not (is_value_term e1) then
                    (** se `e1` não for um valor, avalie-o até que seja *)
                    (match step e1 mem with
                        | Error s -> Error s
                        (** e1 -> e1' => new(e1) -> new(e1') *)
                        | Ok (e1', mem', r) -> 
                            Ok (New e1', 
                                mem', 
                                {name   = "E-New";
                                pre     = ast_of_term e1 ^ ", " ^ string_of_mem mem ^ " -> " ^
                                            ast_of_term e1' ^ ", " ^ string_of_mem ^ mem;
                                post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^
                                            ast_of_term (New e1') ^ ", " ^ string_of_mem ^ mem'} :: r)
                    )
                else
                    (** `e1` = `v1` é um valor, então defina um novo local na memória e associe o valor de `e` ao local na memória *)
                    (match value_of_term e1 with
                    | Some v ->
                        (** definir uma nova posição na memória *)
                        let loc = fresh_loc mem in

                        (** introduzir uma nova entrada (posição, identificador, valor) na memória *)
                        let mem' = (loc, "", v) :: mem in

                        Ok (Location loc, 
                            mem', 
                            {name   = "E-New 1";
                            pre     = string_of_int ^ " não está na memória";
                            post    = "new " ^ ast_of_term e1 ^ ", " ^ string_of_mem ^ mem ^ " -> " ^ 
                                        ast_of_term (Location loc) ^ ", " ^ string_of_mem ^ mem'} :: r)
                    | None -> Error "Não foi possível obter o valor de `e1` em " ^ string_of_term e1)

            (** Dereference !e1
                Dado que `e1` é uma posição na memória, `!e1` avalia para o valor armazenado na memória na localização `e1` *)
            | Derefence e1 ->
                (** se `e1` nao for um valor, avalie-o ate que seja *)
                if not (is_value_term e1) then
                    (match step e1 mem with
                    (** e1 !-> e1' erro' *)
                    | Error s -> Error s
                
                    (** e1 -> e1' => !e1 -> !e1' *)
                    | Ok (e1', mem', r) -> Ok (Derefence e1', mem', r))
                
                else
                    (** `e1` = `v1` é um valor *)
                    (match e1 with
                    (** se `e1` = `v1` é um local de memória (`Location l`) *)
                    | Location l ->
                        (match get mem l with
                            (** se `mem[l]` for vazio, isto é, se `l` não estiver na memória, então erro *)
                            | None -> Error ("derefência: local " ^ string_of_int l ^ " não está na memoria" ^ string_of_int l)
                            
                            (** se `mem[l]` = `(l, s, v)`, então `!e1` avalia para `v` *)
                            | Some (_, _, v) ->
                                (match term_of_value v with
                                    | Some t' ->
                                        Ok (t', 
                                            mem, 
                                            {name   = "E-Deref";
                                            pre     = string_of_int ^ loc ^ " está na memória   mem[" ^ string_of_int ^ loc ^ "] = " ^ ast_of_term t';
                                            post    = "deref " ^ ast_of_term e1 ^ ", " ^ string_of_mem ^ mem ^ " -> " ^ ast_of_term t' ^ ", " ^ string_of_mem ^ mem} :: r)
                                    | None ->
                                        Error "deref: não conseguiu obter o termo da memória"))
                    | _ -> (Error "deref: `e1` não é um local de memória (Location), mas sim " ^ string_of_term e1))

            (* e1; e2   Sequence
            Sequência
            `e1` deve ser avaliado até que se torne Unit.
            Quando `e1` = Unit, então `Sequence (Unit, e2)` é avaliado para `e2` *)
            | Sequence (e1, e2) ->
                (** se `e1` não for um valor, avalie-o até que seja *)
                if not (is_value_term e1) then
                    (match step e1 mem with
                    (** e1 !-> e1', erro. *)
                    | Error s -> Error s
                    
                    (** e1 -> e1' => e1; e2 -> e1'; e2. *)
                    | Ok (e1', mem', r) -> Ok (Sequence (e1', e2), 
                                                mem', 
                                                {name   = "E-Sequence";
                                                pre     = ast_of_term e1 ^ ", " ^ string_of_mem mem ^ " -> " ^ 
                                                            ast_of_term e1' ^ ", " ^ string_of_mem mem';
                                                post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^
                                                            ast_of_term (Sequence (e1', e2)) ^ ", " ^ string_of_mem mem'} ::r))
                else (match value_of_term e1 with
                    (** se `e1` = Unit, então `Sequence (Unit, e2)` é avaliado para `e2` *)
                    | Some Unit -> Ok   (e2,
                                        mem,
                                        {name   = "E-Sequence 1";
                                        pre     = "";
                                        post    = "(); " ^ ast_of_term e2 ^ ", " string_of_mem ^ mem ^ " -> " ^ ast_of_term e2 ^ ", " ^ string_of_mem ^ mem} :: r))
                                        
            (* Location as term should be a value and is handled earlier *)
            | Location _ -> Error "location is a value; no step"
          
            (* Fallback: unknown term form *)
            | _ -> Error ("no small-step rule for term: " ^ ast_of_term e)
(** faz um passo na avaliação de um termo, se for possível
    um passo, na avaliação de um termo `e`,
        sobre uma tabela de símbolos `table`, e
        sobre uma memória `mem`
    
    retorna um passo de avaliação `step_result`
        que pode ser ou um termo `e'` ou um valor `v`
    além da tabela de símbolos e da memória, possivelmente atualizadas,
    e da regra de avaliação usada para provar `e -> e'`
*)
let rec step    (e     :     term)
                (table :  symbols)
                (mem   :   memory)
                :   (term * symbols * memory * rule,
                    value * symbols * memory * rule) result =
    match e with
        (* valores são formais normais e não são avaliados *)
        X| Integer n -> Error (VInteger n, table, mem,
                                {name = "E-Int"; pre = ""; post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value (VInteger n) ^ ", " ^ string_of_mem mem}
                            )

        X| Boolean b -> Error (VBoolean b,
                                table,
                                mem,
                                {name = "E-Bool"; pre = ""; post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value (VBoolean b) ^ ", " ^ string_of_mem mem}
                            )

        X| Unit      -> Error (VUnit,
                            table,
                            mem,
                            {name = "E-Unit"; pre = ""; post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value (VUnit) ^ ", " ^ string_of_mem mem}
                        )
        
        X| Location l -> Error (VLocation l,
                            table,
                            mem,
                            {name = "E-Location"; pre = ""; post = ""})
        
        (** operações binárias:
            avaliação da esquerda para a direita:

            se o primeiro termo (e1) não for um valor, avalie-o até que seja
            se o segundo termo (e2) não for um valor, avalie-o até que seja 
            quando ambos termos forem valores, tente fazer a operação binária *)
        X| BinaryOperation (op, e1, e2) ->
            (** se `e1` não for um valor, isto é, se for possível dar um passo e1 -> e1', então tente dar um passo. *)
            if not (is_value_term e1) then
                (match step e1 table mem  with
                    (** e1 !-> e1', erro. *)
                    | Error s -> Error s

                    (** e1 -> e1' => e1 op e2 -> e1' op e2. *)
                    | Ok (e1', table', mem', r) -> 
                        Ok (BinaryOperation (op, e1', e2),
                            table',
                            mem',
                            {name   = "E-BinOp" ^ string_of_binary_operator op ^ " 1";
                            pre     = ast_of_term e1 ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term e1' ^ ", " ^ string_of_mem mem';
                            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (BinaryOperation (op, e1', e2)) ^ ", " ^ string_of_mem mem'}))
            (** se `e1` = `v1` for um valor, mas `e2` não for um valor, então tente dar um passo e2 -> e2'. *)
            else if not (is_value_term e2) then
                (match step e2 table mem with
                    (** e2 !-> e2', erro. *)
                    | Error s -> Error s

                    (** e2 -> e2' => e1 op e2 -> e1 op e2'. *)
                    | Ok (e2', table', mem', r) -> 
                        Ok (BinaryOperation (op, e1, e2'),
                            table',
                            mem',
                            {name   = "E-Binop" ^ string_of_binary_operator op ^ " 2";
                            pre     = ast_of_term e2 ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term e2' ^ ", " ^ string_of_mem mem';
                            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (BinaryOperation (op, e1, e2')) ^ ", " ^ string_of_mem mem'}))

            (** são valores `e1` = `v1` e `e2` = `v2`. *)
            else (match (value_of_term e1, value_of_term e2) with
                    | (Some v1, Some v2) ->
                        (** aplique a função para computar o resultado de uma operação binária. *)
                        let result_value = apply_binop op v1 v2 in
                        
                        (** apply_binop sempre retorna um valor.
                            pdoe ser um valor real, ou um erro (EvaluationError) *)
                        (match result_value with 
                            |   EvaluationError s -> Error (EvaluationError s, table, mem, {
                                    name = "E-Binop Error";
                                    pre  = "";
                                    post = s;
                            })

                            |   v -> Error (v, table, mem, {
                                    name = "E-Binop";
                                    pre  = ast_of_term e1 ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value v1 ^ ", " ^ string_of_mem mem ^ ", " ^
                                            ast_of_term e2 ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value v2 ^ ", " ^ string_of_mem mem ^ ", ";
                                    post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ string_of_value v ^ ", " ^ string_of_mem mem;
                            })
                        )
                    
                    |  _ -> Error (EvaluationError ("Não foi possível avaliar " ^ ast_of_term e),
                            table, mem,
                            {name = "E-Binop Error 1";
                            pre     = "";
                            post    = "";
                            })
            )


        (** if(e1, e2, e3) Conditional
            avaliação da esquerda para direita:

            se e1 não for um valor, avalie-o até que seja;
            se e1 for verdadeiro, então retorne e2;
            se e1 for falso     , então retorne e3
            [se e1 for um valor não booleano, erro]
        *)
        X| Conditional (e1, e2, e3) ->
            (** e1 -> e1' => if(e1, e2, e3) -> if(e1', e2, e3) *)
            if not (is_value_term e1) then
                (match step e1 table mem with
                (** e1 !-> e1' => erro *)
                | Error s -> Error s
                
                (** e1 -> e1' => if(e1, e2, e3) -> if(e1', e2, e3) *)
                | Ok (e1', table', mem', r) -> 
                    Ok  (Conditional (e1', e2, e3), 
                        table',
                        mem', 
                        {name   = "E-If 3";
                        pre     =   ast_of_term e1 ^ ", " ^ string_of_mem mem ^ " -> " ^
                                    ast_of_term e1' ^  ", " ^ string_of_mem mem';
                        post    =   ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^
                                    ast_of_term (Conditional (e1', e2, e3)) ^  ", " ^ string_of_mem mem'}))
            else
                (* `e1` = `v1` é um valor *)
                (match value_of_term e1 with
                    (** se `v1` for verdadeiro, então retorne `e2`. *)
                    | Some (VBoolean true) -> Ok (e2, table, mem, {
                        name    = "E-If (1) True";
                        pre     = "";
                        post    = "if true then " ^ ast_of_term e2 ^ " else " ^ ast_of_term e3 ^ ", " ^ string_of_mem mem ^ " -> " ^ 
                                    ast_of_term e2 ^ ", " ^ string_of_mem  mem})

                    (** se `v1` for falso, então retorne `e3`. *)
                    | Some (VBoolean false) -> Ok (e3, table, mem, {
                        name    = "E-If (2) False";
                        pre     = "";
                        post    = "if false then " ^ ast_of_term e2 ^ " else " ^ ast_of_term e3 ^ ", " ^ string_of_mem mem ^ " -> " ^ 
                                    ast_of_term e3 ^ ", " ^ string_of_mem  mem})

                    (** se `v1` for um valor não booleano, erro. *)
                    | _ -> Error (EvaluationError ("Não foi possivel avaliar " ^ ast_of_term e),
                        table, mem,
                        {name = "E-If Error";
                        pre  = "";
                        post = "";
                        })
                )

        (* e1; e2   Sequence
            Sequência
            `e1` deve ser avaliado até que se torne Unit.
            Quando `e1` = Unit, então `Sequence (Unit, e2)` é avaliado para `e2` *)
        X| Sequence (e1, e2) ->
            (** se `e1` não for um valor, avalie-o até que seja *)
            if not (is_value_term e1) then
                (match step e1 table mem with
                (** e1 -> e1' => e1; e2 -> e1'; e2. *)
                | Ok (e1', table', mem', r) -> Ok (Sequence (e1', e2), 
                                            table',
                                            mem', 
                                            {name   = "E-Sequence";
                                            pre     = ast_of_term e1 ^ ", " ^ string_of_mem mem ^ " -> " ^ 
                                                        ast_of_term e1' ^ ", " ^ string_of_mem mem';
                                            post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^
                                                        ast_of_term (Sequence (e1', e2)) ^ ", " ^ string_of_mem mem'}))
            else (match value_of_term e1 with
                (** se `e1` = Unit, então `Sequence (Unit, e2)` é avaliado para `e2` *)
                | Some VUnit -> Ok   (e2,
                                    table,
                                    mem,
                                    {name   = "E-Sequence 1";
                                    pre     = "";
                                    post    = "(); " ^ ast_of_term e2 ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term e2 ^ ", " ^ string_of_mem mem}))
                | _ -> Error (EvaluationError ("`e1` deve ser avaliado para Unit em uma sequência `e1; e2`"),
                    table, mem, {name = "E-Seq Error"; pre = ""; post = ""})
            
    
        (** while e1 do e2
            comando while é avaliado expandindo-o para um if com e1, e2 e Unit *)
        X| While (e1, e2) ->
            let expanded = Conditional (e1, Sequence (e2, While (e1, e2)), Unit) in
            Ok (expanded,
                table,
                mem, 
                {name   = "E-While";
                pre     = "";
                post    = ast_of_term e ^ ", " ^ string_of_mem  mem ^ " -> " ^ ast_of_term expanded ^ ", " ^ string_of_mem mem })

        (** Let
            Definir variáveis e atribuir valores a elas.
            A expressão Let (x, t, e1, e2) irá
            
            1.  Adicionar o nome do identificador à tabela de símbolos 
            2.  Avaliar `e1` até que seja um valor
            3.  Associar o valor `v1` à posição de memória `l`,
                obtida a partir da tabela de símbolos
            4.  Substituir toda ocorrência de `x` em `e2` por `v1`.

            NÃO é possível fazer dois Let com o mesmo identificador;

                let x : Int = 1 in
                    let x : Bool = 2 in ...
            
            Para modificar o VALOR de um termo, é neessário usar atribuição
            (assignment)
                let x : Int = 1 in
                    x := 2; ...

            NÃO é possível fazer atribuição de um valor de tipo distinto,
            isto é tratado em Assignment (e1, e2).
        *)
        X| Let (x, t, e1, e2) ->
    
        (** Identificador x
            Variáveis.
            
            Um identificador é avaliado para um valor armazenado na memória. 
            
            Identifier x -> (Dereference (Location l)) *)
        X| Identifier x -> 
            (* acessa a tabela de símbolos para verificar se `x` está lá *)
            if is_bound x table then
                match search x table with
                | Some l -> Ok (Dereference (Location l), table, mem, {
                    name    = "E-Id";
                    pre     = "";
                    post    = x ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (Dereference (Location l)) ^ ", " ^ string_of_mem mem})
                | None -> Error (EvaluationError ("Identificador não declarado: `" ^ x ^ "`"),
                    table, mem,
                    {name = "E-Id Error";
                    pre  = "";
                    post = "";
                    })
            else Error (EvaluationError ("Identificador não declarado: `" ^ x ^ "`"),
                table, mem, {
                    name = "E-Id Error";
                    pre  = "";
                    post = "";
                })

        (** Dereferência
            !e : recupera o valor que está na posição de memória que `e` aponta 
            
            `e` deve ser (VLocation l) *)
        X| Dereference e ->
            (** avaliação esq. -> dir.;
                se `e` não é um valor, então avalie-o até que seja *)
            if not (is_value_term e) then (match step e table mem with
                | Ok (e', table', mem', r) -> Ok (Dereference e', table', mem', {
                        name    = "E-Deref";
                        pre     = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term e' ^ ", " ^ string_of_mem mem';
                        post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (Dereference e') ^ ", " ^ string_of_mem mem'}))
                
            (** se for um valor, então verifique se é uma VLocation l *)
            else (match value_of_term e with
                (** `e` é um valoe e `e` = `l` é uma localização na memória *)
                | Some (VLocation l) -> (
                    (** verifique se a posiçãao `l` realmente existe na memória *)
                    if (exists l mem) then
                        (** se existir, então recupere o valor associado à `l` na memória
                            pois este é o valor apontado pela variável `e` (Identifier x) *)
                        (match get l mem with
                            |   Some v -> (match term_of_value v with
                                |   Some t -> Ok (t, table, mem, {
                                    name    = "E-Deref 1";
                                    pre     = "";
                                    post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term t ^ ", " ^ string_of_mem mem})

                                |   None -> Error (EvaluationError ("Nao foi possivel avaliar " ^ ast_of_term e),
                                    table, mem,
                                    {name = "E-Deref Error";
                                    pre  = "";
                                    post = "";
                                    })))
                    else Error (EvaluationError ("Nao foi possivel avaliar " ^ ast_of_term e),
                        table, mem,
                        {name = "E-Deref Error";
                        pre  = "";
                        post = "";
                        })))
        
        (** new e 
            se `e` não for um valor, avalie-o até que seja;
            se `e` for um valor,
                defina um novo local na memória
                associe o valor de `e` ao local na memória
            a avaliação de `new e` produz o local da memória `l` *)
        X| New e ->
            (** `e` não é um valor, então avalie-o até que seja *)
            if not (is_value_term e) then (match step e table mem with
                | Ok (e', table', mem', r) -> Ok (New e', table', mem', {
                        name    = "E-New";
                        pre     = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term e' ^ ", " ^ string_of_mem mem';
                        post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (New e') ^ ", " ^ string_of_mem mem'}))
            
            (** `e` = `v` é um valor, então crie uma nova posição na memória e associe `v` a ela *)
            else (match value_of_term e with
                | Some v -> (
                    (* ordene a memória | localização *)
                    let mem' = sort mem in

                    (* associe `v` a um novo local na memória `l` *)
                    let l = where mem' in
                    let mem'' = set l v mem' in

                    (* retorne `l` enquanto termo *)
                    Ok (Location l, table, mem'', {
                        name    = "E-New 1";
                        pre     = "";
                        post    = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " ^ ast_of_term (Location l) ^ ", " ^ string_of_mem mem''})
                    )
                
                | None -> Error (EvaluationError ("Nao foi possivel avaliar " ^ ast_of_term e),
                    table, mem,
                    {name = "E-New Error";
                    pre  = "";
                    post = "";
                    }))

(** `stepn` avalia um termo até que retorne um valor ou um erro.

    em `step` :
    isto é feito tratanto tanto erros reais quanto valores como Error em um objeto result;
    dessa forma, temos  Ok (term, ...)      enquanto a avaliação está ocorrendo, e
                        Error (value, r)    quando a avaliação para, por algum motivo.
    
    tanto durante a avaliação quanto quando acaba a avaliação,
    são passados objetos tabela de símbolos e memória e a regra de avaliação usada.

    aqui, em `stepn`:
    o tipo resultado é  Ok          (termo, tabela de símbolos, regra)
                        ou Error    (mensagem de erro)
    porque queremos imprimir termos ou strings no interpretador.

    uma `evaluation` é uma lista de regras, aliás `rule list`.
*)
let rec stepn       (e       :       term)
                    (mem    :     memory)
                    (table  :    symbols)
                    (limit  :        int)
                    (rules  : evaluation)
                        :   (term * symbols * memory * evaluation, 
                            value * symbols * memory * evaluation) result =
    if (limit <= 0) then Error (EvaluationError "limite de passos atingido", table, mem, rules)
    else
        match step e table mem with
            | Error (v, t, m, r)    -> Error (v, t, m, r :: rules)
            | Ok (e', t, m, r)      -> stepn e' m t (limit - 1) (r :: rules)
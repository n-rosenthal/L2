(**
    `src/Terms.ml`
    
    Definição da sintaxe de termos e de valores para a linguagem `L2`

    1.  VALORES
    São termos (expressões) EQUIVALENTES A valores (isto é, formais normais ou presas/stuck):
      `Integer`, `Boolean`, `Unit`, `Location`
      Estes valores são tipados imadiatamente para os tipos:
        `Int`, `Bool`, `Unit`, `Reference Int`
      e são avaliados imediatamente para os valores:
        `VInteger`, `VBoolean`, `VUnit`, `VLocation l`
  
    2.  Identificadores (variáveis)
    `Identifier x` (x:string) representa um identificador de variável.

    3.  If (e1, e2, e3) = Conditional (e1, e2, e3)
    Tipo: e1 : Bool, e2 : T, e3 : T   [com T =T] => If(e1, e2, e3) : T
    Eval:   se e1 -> VBoolean true, então If(e1, e2, e3) -> e2
            se e1 -> VBoolean false, então If(e1, e2, e3) -> e3
    
    4.  Operações Binárias (bop, e1, e2) = BinaryOperation (bop, e1, e2)
    Tipo: e1 : T, e2 : T => bop : T'  [o tipo do resultado depende da operação;]
    Eval: [depende do tipo de operação, mas e1 -> v1, e2 -> v2 então (bop, v1, v2) -> v]

    5.   while e1 do e2
    O comando while é expandido da seguinte forma na avaliação:
    While (e1, e2) -> Conditional (e1, 
                                    Sequence (e2, 
                                            While (e1, e2)), 
                                    Unit)

    Se a condição do while (cond, e1) for verdadeira, então faça e2 (body)
    e depois faça while (e1, e2) de novo. Se a condição do while (cond, e1)
    for falsa, então Unit, fim do laço.

    Tipo: e1 : Bool, e2 : T => While(e1, e2) : Unit

    6.  e1; e2
        Sequence (e1, e2)
        Em uma sequência, esperamos que o primeiro termo seja avaliado inteiramente até tornar-se Unit.
        Isto é assim porque queremos que os componentes de uma sequência sejam comando imperativos que terminam em Unit.
        O tipo de `e1; e2` é o tipo daquilo que virá em `e2`. A avaliação de `e1; e2` -> `Unit; e2` -> `e2`

        São comandos que terminam em unit:
            1.  while e1 do e2
            2.  e1 := e2        (atribuição, assignment)
            3.  unit            (sic)
    
        Tipo: e1 : Unit, e2 : T => Sequence(e1, e2) : T

        Avaliação: Se e1 -> Unit, então Sequence(e1, e2) -> e2
    
    7.  e1 := e2
        Assignment (e1, e2), atribuir a um identificador `e1` um valor `e2`.

    8.  let x : T = e1 in e2
        Let (x, T, e1, e2)
        Definir variáveis e atribuir valores a elas.
        A expressão Let (x, t, e1, e2) irá
            1.  Adicionar o nome do identificador à tabela de símbolos 
            2.  Avaliar `e1` até que seja um valor
            3.  Associar o valor `v1` à posição de memória `l`,
            4.  Substituir toda ocorrência de `x` em `e2` por `v1`.

        NÃO é possível fazer dois Let com o mesmo identificador;

            let x : Int = 1 in
                let x : Bool = 2 in ...
        
        Para modificar o VALOR de um termo, é neessário usar atribuição
        (assignment)
            let x : Int = 1 in
                x := 2; ...
    
    9.  new e
        New (e)
        A expressão new e irá
            1.  Avaliar `e` até que seja um valor
            2.  Criar uma nova posição na memória
            3.  Associar o valor `v1` à nova posição de memória `l`,
            4.  Substituir toda ocorrência de `x` em `e2` por `v1`.
            5.  Avaliar para a posição `l` na memória

    10. !e
        Dereference (e)
        A expressão !e irá
            1.  Avaliar `e` até que seja um valor
            2.  Se `e` é um (Identifier x`, então ...

    11. ()
        Unit

    12. e1; e2
        Sequence (e1, e2)
    
    13. l
        Location (l)
    
*)

open Types

(** sintaxe de termos sobre `L2` *)
type term =
    | Integer of int                                (* n, termo número inteiro *)
    | Boolean of bool                               (* b, termo booleano *)
    | Identifier of string                          (* x, identificador *)
    | Conditional of term * term * term             (* If, operador condicional *)
    | BinaryOperation of binary_operator * term * term    (* bop, operação binária *)
    | While of term * term                          (* While e1 do e2 *)
    | Assignment of term * term                     (* x := e *)
    | Let of string * tipo * term * term            (* let x: T = e1 in e2 *)
    | New of term                                   (* new e *)
    | Dereference of term                           (* !e *)
    | Unit                                          (* () *)
    | Sequence of term * term                       (* e1; e2 *)
    | Location of int                               (* l, local de memória *)
and binary_operator = 
      | Add | Sub | Mul | Div                       (* operadores aritméticos *)
      | Eq  | Neq | Lt  | Leq | Gt | Geq            (* operadores relacionais *)
      | And | Or                                    (* operadores lógicos *)
;;



(** sintaxe de valores sobre `L2` *)
type value =
    | VInteger of int                               (* n, valor número inteiro *)
    | VBoolean of bool                              (* b, valor booleano *)
    | VUnit                                         (* (), unit *)
    | VLocation of int                              (* l, local de memória *)
    | EvaluationError of string                     (* s, erro de avaliação *)
and name_binding = string * value                   (* associação entre um identificador e um valor *)
;;

#   Sintaxe de termos
Sejam $\Gamma$ o ambiente de tipos e seja $\sigma$ a memória e $\text{símbolos}$ a tabela de símbolos.

```ocaml
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
    | Derefence of term                             (* !e *)
    | Unit                                          (* () *)
    | Sequence of term * term                       (* e1; e2 *)
    | Location of int                               (* l, local de memória *)
and binary_operator = 
      | Add | Sub | Mul | Div                       (* operadores aritméticos *)
      | Eq  | Neq | Lt  | Leq | Gt | Geq            (* operadores relacionais *)
      | And | Or                                    (* operadores lógicos *)
;;
```


##  Valores
Ver `src/Terms.ml`

Não existem propriamente, em $L_2$, *regras de avaliação* para *valores*, uma vez que valores são termos já avaliados; são formais normais ou presas, *stuck*. 

São valores os termos

```ocaml
type term = ..
    | Integer of int        (*  termo número inteiro *)
    | Boolean of bool       (*  termo booleano *)
    | Unit                  (*  termo unitário *)
    | Location of int       (*  local de memória *)
```

Estes termos são imediatamente avaliados para seus respectivos valores.

```ocaml
(** sintaxe de valores sobre `L2` *)
type value =
    | VInteger of int                               (* n, valor número inteiro *)
    | VBoolean of bool                              (* b, valor booleano *)
    | VUnit                                         (* (), unit *)
    | VLocation of int                              (* l, local de memória *)
    | EvaluationError of string                     (* s, erro de avaliação *)
and name_binding = string * value                   (* associação entre um identificador e um valor *)
;;
```

O termo `Location` e o valor `VLocation` são discutidos `docs/outras_coisas.md`#memória.

Note que `EvaluationError` não é um termo da linguagem $L_2$. Ao contrário, `EvaluationError` é definido somente na sintaxe dos *valores*. `EvaluationError` não é um valor da linguagem `L_2`, também, mas é o valor resultante da avaliação de um termo mal-formado ou que a avaliação falhou.

### Funções *helper*
1. `is_value_term`: $\text{term} \to \mathbb{B}$, verifica se um termo representa um valor.
2. `value_of_term`: $\text{term} \to \text{value} \to \mathbb{B}$, converte um termo para um valor, (caso `is_value_term e` retorne verdadeiro para `e`).
3. `term_of_value`: $\text{value} \to \text{term} \to \mathbb{B}$, converte um valor para um termo, (caso `value_of_term e` retorne verdadeiro para `e`).
4. `substitute` $\text{string} \times \text{value} \times \text{term} \to \text{term}$, substitui um identificador por um valor em um termo. {x/v}e.

### Regras de Avaliação
Artificialmente, definimos as regras de avaliação para valores, a fim de, ao imprimí-las em tela, sabermos em que ponto da avaliação foi produzido o valor.

$$
\frac{}
     {\text{Integer n}, \ \sigma \ \to \text{VInteger n}, \ \sigma}
\;(\text{E-Int})
$$

$$
\frac{}
     {\text{Boolean b}, \ \sigma \ \to \text{VBoolean b}, \ \sigma}
\;(\text{E-Bool})
$$

$$
\frac{}
     {\text{Unit}, \ \sigma \ \to \text{VUnit}, \ \sigma}
\;(\text{E-Unit})
$$

$$
\frac{}
     {\text{Location l}, \ \sigma \ \to \text{VLocation l}, \ \sigma}
\;(\text{E-Location})
$$

```ocaml
(** faz um passo na avaliação de um termo, se for possível *)
let rec step    (e     :    term)
                (mem   :  memory)
                : (term * memory * eval_rule, string) result =
    match e with 
    ...
    |   Integer n -> Ok (VInteger n, mem, {
                            name = "E-Int";
                            pre  = "";
                            post =  ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " 
                            ^ string_of_value (VInteger n) ^ ", " ^ string_of_mem mem
                        })
    
    |   Boolean b -> Ok (VBoolean b, mem, {
                            name = "E-Bool";
                            pre  = "";
                            post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " 
                            ^ string_of_value (VBoolean b) ^ ", " ^ string_of_mem mem
    })

    |   Unit      -> Ok (VUnit, mem, {
                            name = "E-Unit";
                            pre  = "";
                            post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " 
                            ^ string_of_value (VUnit) ^ ", " ^ string_of_mem mem
    })

    |   Location l -> Ok (VLocation l, mem, {
                            name = "E-Location";
                            pre  = "";
                            post = ast_of_term e ^ ", " ^ string_of_mem mem ^ " -> " 
                            ^ string_of_value (VLocation l) ^ ", " ^ string_of_mem mem
    })

    ...
```

##  Identificadores (variáveis, `Identifier x`)
### Inferência de Tipo

$$
\frac{
  x : T \in \Gamma
}{
  \Gamma \vdash x : T
}
\quad\text{(T-Var)}
$$

Se o identificador `x` estiver no ambiente de tipos `Γ` com o tipo `T`, então o tipo do identificador `x` é `T`.

### Avaliação

$L_2$ não define explicitamente a avaliação de identificadores.

Identificadores são as variáveis que o programador define em seus programas. Estas variáveis são mapeadas em uma *tabela de símbolos*, que é uma lista de pares (`identificador`: $\text{string}$ $\times$ `localização na memória`: $\text{int}$). Um identificador **não** é o valor que ele aponta. Ao contrário, um identificador **avalia para** a **posição na memória** *apontada* por ele.

Se `x` estiver na *tabela de símbolos*, então `Identifier x` avalia para o valor posição *na memória* `VLocation l` para o qual `x` aponta. Se `x` não estiver na *tabela de símbolos*, então `Identifier x` avalia para `EvaluationError`.

$$
\frac{
    \text{x} \in \text{símbolos}, \ \sigma
}{
    \sigma \vdash \text{Identifier x} \to \text{VLocation} \ l 
}
\quad\text{(E-Var)}
$$ 

---

##  Condicional (`if e1 then e2 else e3`)
Sintaxe: `Conditional (e1, e2, e3)`

### Inferência de Tipo
A expressão condicional exige que:
- a condição $e_1$ tenha tipo $\texttt{Bool}$;
- ambos os ramos $e_2$ e $e_3$ tenham o $\textbf{mesmo tipo}$ $T$.

A regra formal é:

\[
\frac{
  \Gamma \vdash e_1 : \text{Bool}
  \qquad
  \Gamma \vdash e_2 : T
  \qquad
  \Gamma \vdash e_3 : T
}{
  \Gamma \vdash \text{if } e_1 \text{ then } e_2 \text{ else } e_3 : T
}
\quad (\text{T-If})
\]

Se $e_1$ não for booleano, ou se $e_2$ e $e_3$ tiverem tipos distintos, então a expressão não tem tipo válido.

### Avaliação
A avaliação do condicional funciona assim:

- Primeiro reduzimos a condição $e_1$, caso ela ainda não seja um valor.
- Se $e_1$ reduz para $\texttt{true}$, escolhemos o ramo $e_2$.
- Se $e_1$ reduz para $\texttt{false}$, escolhemos o ramo $e_3$.

As regras formais são as seguintes:

\[
\frac{
  e_1 \to e_1'
}{
  \text{if } e_1 \text{ then } e_2 \text{ else } e_3
  \;\to\;
  \text{if } e_1' \text{ then } e_2 \text{ else } e_3
}
\quad(\text{E-IfStep})
\]

\[
\frac{}{
  \text{if true then } e_2 \text{ else } e_3
  \;\to\;
  e_2
}
\quad(\text{E-IfTrue})
\]

\[
\frac{}{
  \text{if false then } e_2 \text{ else } e_3
  \;\to\;
  e_3
}
\quad(\text{E-IfFalse})
\]

O condicional avalia primeiro a condição.  
Se ela for verdadeira, retorna o ramo $\texttt{then}$.  
Se for falsa, retorna o ramo $\texttt{else}$.  
Se ainda não for um valor booleano, a condição é reduzida antes de continuar.

---

##  Operações Binárias (`BinaryOperation(op, e1, e2)`)
Sintaxe: `BinaryOperation (op, e1, e2)`

### Inferência de Tipo

A regra de tipos para operações binárias depende do operador `op`.  
Dividimos em três classes:

1. **Operadores aritméticos:** `+`, `-`, `*`, `/`, `mod`  
   - Ambos os operandos devem ser do tipo `Int`
   - O resultado é `Int`

\[
\frac{
  \Gamma \vdash e_1 : \text{Int}
  \qquad
  \Gamma \vdash e_2 : \text{Int}
}{
  \Gamma \vdash e_1 \;\text{op}\; e_2 : \text{Int}
}
\quad(\text{T-BinOp \ \{+, -, *, /, mod\}})
\]

2. **Operadores booleanos:** `and`, `or`  
   - Ambos os operandos devem ser `Bool`
   - O resultado é `Bool`

\[
\frac{
  \Gamma \vdash e_1 : \text{Bool}
  \qquad
  \Gamma \vdash e_2 : \text{Bool}
}{
  \Gamma \vdash e_1 \;\text{op}\; e_2 : \text{Bool}
}
\quad(\text{T-BinOp \ \{and, or\}})
\]

3. **Operadores relacionais:** `=`, `<>`, `<`, `<=`, `>`, `>=`  
   - Ambos os operandos devem ser `Int`
   - O resultado é `Bool`

\[
\frac{
  \Gamma \vdash e_1 : \text{Int}
  \qquad
  \Gamma \vdash e_2 : \text{Int}
}{
  \Gamma \vdash e_1 \;\text{op}\; e_2 : \text{Bool}
}
\quad(\text{T-BinOp \ \{=, <>, <, <=, >, >=\}})
\]

Também é possível comparar booleanos com `==` e `<>`.

Se os tipos não coincidirem com o esperado pelo operador, a expressão binária não tem tipo válido.

---

### Avaliação

A avaliação segue a ordem esquerda–direita:

1. Reduzimos `e1` até virar um valor.  
2. Depois reduzimos `e2`.  
3. Quando ambos são valores, aplicamos o operador.

As regras formais são:

\[
\frac{
  e_1 \to e_1'
}{
  \text{op}(e_1, e_2)
  \;\to\;
  \text{op}(e_1', e_2)
}
\quad(\text{E-BinOp 1})
\]

\[
\frac{
  e_2 \to e_2'
}{
  \text{op}(v_1, e_2)
  \;\to\;
  \text{op}(v_1, e_2')
}
\quad(\text{E-BinOp 2})
\]

E quando ambos os operandos são valores:

\[
\frac{}{
  \text{op}(v_1, v_2) \;\to\; v
}
\quad(\text{E-BinOp})
\]

onde `v` é o resultado da computação real do operador sobre os valores `v₁` e `v₂`, por exemplo:

- `1 + 2 → 3`
- `4 < 2 → false`
- `true and false → false`

**Ordem de avaliação**: operações binárias avaliam sempre primeiro o lado esquerdo, depois o direito, e finalmente aplicam o operador quando ambos os operandos forem valores.

---

##  Comando de Atribuição (`Assignment(x, e)`)
Sintaxe: `Assignment (Identifier x, e)`  
Semântica: **modifica a memória**, armazenando o valor de `e` na posição referenciada por `x`.

### Inferência de Tipo

Para que a atribuição seja válida:

1. `x` deve ter tipo `ref T` no ambiente.  
2. `e` deve ter tipo `T`.  
3. O comando retorna tipo `Unit`.

A regra formal é:

\[
\frac{
  \Gamma \vdash x : \text{Ref}\;T
  \qquad
  \Gamma \vdash e : T
}{
  \Gamma \vdash x := e : \text{Unit}
}
\quad(\text{T-Atr})
\]

Se `x` não for uma referência, ou `e` não tiver o tipo apontado por `x`, a atribuição é inválida.

### Avaliação

A avaliação segue a ordem:

1. Avaliamos `x` **até obter a localização** `l`.
2. Avaliamos `e` até obter o valor `v`.
3. Escrevemos `v` na memória no endereço `l`.
4. O comando retorna `Unit`.

Regras formais:

Avaliar o lado esquerdo:

\[
\frac{
  x \to x'
}{
  x := e \;\to\; x' := e
}
\quad(\text{E-Atr})
\]

Avaliar o lado direito:

\[
\frac{
  e \to e'
}{
  l := e \;\to\; l := e'
}
\quad(\text{E-Atr})
\]

Quando ambos lados são valores:

\[
\frac{}{
  l := v \;\to\; \text{store}(l \mapsto v);\; \text{VUnit}
}
\quad(\text{E-Atr})
\]

A atribuição **muda a memória** e é avalia para **valor** `VUnit`.

---

##  Laço `while` (`While(e1, e2)`)
Sintaxe: `While (e1, e2)`  
Semântica: Enquanto a condição `e1` for verdadeira, executar o corpo `e2`.

### Inferência de Tipo

Para um `while` ser bem tipado:

- a condição `e1` deve ser `Bool`;
- o corpo `e2` deve ter tipo `Unit`;
- o tipo da expressão inteira é `Unit`.

\[
\frac{
  \Gamma \vdash e_1 : \text{Bool}
  \qquad
  \Gamma \vdash e_2 : \text{Unit}
}{
  \Gamma \vdash \text{while } e_1 \text{ do } e_2 : \text{Unit}
}
\quad(\text{T-While})
\]

### Avaliação

Um `while` é açúcar sintático para:

\[
\text{while } e_1 \text{ do } e_2
\quad\equiv\quad
\text{if } e_1 \text{ then } (e_2 ; \text{while } e_1 \text{ do } e_2) \text{ else Unit}
\]

A avaliação segue a mesma estratégia:

1. Avaliamos `e1`.  
2. Se `e1 → true`, então avaliamos `e2` e depois repetimos o loop.  
3. Se `e1 → false`, o laço termina retornando `Unit`.

Regras formais:

Passo sobre a condição:

\[
\frac{
  e_1 \to e_1'
}{
  \text{while } e_1 \text{ do } e_2
  \;\to\;
  \text{while } e_1' \text{ do } e_2
}
\quad(\text{E-While Step})
\]

Caso verdadeiro:

\[
\frac{}{
  \text{while true do } e_2
  \;\to\;
  e_2;\;\text{while true do } e_2
}
\quad(\text{E-While True})
\]

Caso falso:

\[
\frac{}{
  \text{while false do } e_2
  \;\to\;
  \text{Unit}
}
\quad(\text{E-While False})
\]

Assim como em linguagens imperativas reais, o laço `while` produz sempre `Unit` — ele serve apenas para efeitos colaterais na memória.

---

##  Sequência de Comandos (`e1 ; e2`)
Sintaxe: `Sequence (e1, e2)`  
Semântica: **Avalia** `e1`, ignora seu valor (que deve ser `Unit`), e depois avalia `e2`, cujo valor é o resultado da sequência.

### Inferência de Tipo

Para uma sequência ser bem tipada:

1. `e1` deve ter tipo `Unit`.
2. `e2` pode ter qualquer tipo `T`.
3. O tipo da sequência é o tipo de `e2`.

Regra formal:

\[
\frac{
  \Gamma \vdash e_1 : \text{Unit}
  \qquad
  \Gamma \vdash e_2 : T
}{
  \Gamma \vdash e_1 ; e_2 : T
}
\quad(\text{T-Sequence})
\]

A restrição de que `e1` deve ser `Unit` garante que apenas comandos com efeitos colaterais (como atribuições, loops, etc.) possam aparecer na primeira posição. Valores como inteiros ou booleanos não são permitidos.

### Avaliação

A avaliação segue a ordem estrita da esquerda para direita:

1. Avaliamos `e1` até obter `Unit`.
2. Avaliamos `e2` e retornamos seu valor.

Regras formais:

Avaliar o primeiro comando:
\[
\frac{
  e_1 \to e_1'
}{
  e_1 ; e_2 \;\to\; e_1' ; e_2
}
\quad(\text{E-Seq Step})
\]

Quando o primeiro comando é `Unit`:
\[
\frac{
}{
  \text{Unit} ; e_2 \;\to\; e_2
}
\quad(\text{E-Seq})
\]

Se `e1` avaliar para um valor diferente de `Unit`, ocorre erro de tipo em tempo de execução.



---

##  Declaração Local `let x : T = e1 in e2`
Sintaxe: `Let (x, T, e1, e2)`  
Semântica: **Vincula** o identificador `x` ao valor de `e1` e avalia `e2` no contexto estendido. O comportamento difere se `T` for tipo referência (`ref T'`) ou tipo não-referência.

### Inferência de Tipo

Para um `let` ser bem tipado:

1. A expressão `e1` deve ter tipo `T` no ambiente atual.
2. O corpo `e2` é avaliado no ambiente estendido com `x : T`.
3. O tipo do `let` é o tipo de `e2` no ambiente estendido.

Regra formal:

\[
\frac{
  \Gamma \vdash e_1 : T
  \qquad
  \Gamma, x:T \vdash e_2 : U
}{
  \Gamma \vdash \text{let } x : T = e_1 \text{ in } e_2 : U
}
\quad(\text{T-Let})
\]

A inferência de tipos em L2 inclui:
- Para **tipos não-referência** (`int`, `bool`, `unit`): O tipo de `e1` deve coincidir exatamente com `T`.
- Para **tipos referência** (`ref T`): O tipo de `e1` também deve ser `ref T`.

### Avaliação

A avaliação segue duas estratégias distintas:

#### Para tipos **não-referência**:
1. Avaliamos `e1` até obter um valor `v`.
2. Substituímos todas as ocorrências livres de `x` em `e2` por `v`.
3. Avaliamos a expressão resultante.

Regras:
\[
\frac{
  e_1 \to e_1'
}{
  \text{let } x : T = e_1 \text{ in } e_2
  \;\to\;
  \text{let } x : T = e_1' \text{ in } e_2
}
\quad(\text{E-Let-Step})
\]

\[
\frac{
  \text{valor}(v_1) \quad T \neq \text{Ref}\;T'
}{
  \text{let } x : T = v_1 \text{ in } e_2
  \;\to\;
  e_2[v_1/x]
}
\quad(\text{E-Let-Subst})
\]

#### Para tipos **referência**:
1. Avaliamos `e1` até obter um valor `VLocation(l)`.
2. Estendemos a tabela de símbolos para associar `x` à localização `l`.
3. Avaliamos `e2` com esta nova associação.

Regra:
\[
\frac{
  \text{valor}(VLocation(l)) \quad T = \text{Ref}\;T'
}{
  \text{let } x : T = VLocation(l) \text{ in } e_2
  \;\to\;
  e_2 \quad \text{(com } x \mapsto l \text{ no ambiente)}
}
\quad(\text{E-Let-Ref})
\]

Se `e1` não for uma localização quando `T` é referência, ocorre erro de tipo em tempo de execução.

---

## Criação de Referência (new e)
Sintaxe: `New e`
**Aloca** uma nova posição $l$ na memória, armazena o valor de `e` nessa posição e retorna a localização $l$.

### Inferência de Tipo
$$
\frac{
  \Gamma \vdash e : T
}{
  \Gamma \vdash \text{new } e : \text{Ref}\;T
}{\text{(T-New)}}
$$

### Avaliação
A expressão e pode ser qualquer termo válido: um valor, variável, ou expressão complexa. O tipo de e determina o tipo da referência criada.
Avaliação

A avaliação segue a ordem:

1. Avaliamos `e` até obter um valor `v`.
2. Alocamos uma **nova** posição $l$ na memória $\sigma$.
3. Armazenamos `v` na célula $l$.
4. Retornamos a localização $l$ como valor `VLocation l`.

Regras formais:
Enquanto `e` não é um valor, avalie-o até que seja.

$$
\frac{
  e \to e'
}{
  \text{new } e
  \;\to\;
  \text{new } e'
}
\quad(\text{E-New Step})
$$

Quando `e`for um valor, alocar nova posição na memória:

$$
\frac{
    l \notin \text{Dom}( \sigma )
}{
    \text{new } e, \ \sigma \to \text{VLocation l}, \ \sigma [l \mapsto v]
}
\quad(\text{E-New 1})
$$

---

##  Dereferência (desreferenciação) `!e`
Sintaxe: `Dereference e`
**Acessa** o valor armazenado na localização referenciada `e`.
A expressão e deve ser uma referência.

### Inferência de Tipo
Para que `!e` seja bem tipado, é necessário que

1. `e` seja tipado em `ref t`
2.  o tipo de `!e` seja `t`.

$$
\frac{
  \Gamma \vdash e : \text{Ref}\;T
}{
  \Gamma \vdash \text{!}e : T
}{\text{(T-Deref)}}
$$

### Avaliação
A avaliação segue os passos:

1. Avaliamos `e` até obter uma localização `VLocation(l)`.
2. Consultamos a memória no endereço $l$ para obter o valor `v` armazenado.
3. Retornamos `v`.

Regras formais:

$$
\frac{
  e \to e'
}{
  \text{!}e
  \;\to\;
  \text{!}e'
}{\text{(E-Deref Step)}}
$$

$$
\frac{
  l \in \text{Dom}( \sigma ) \quad \land \quad \sigma(l) = v
}{
  \text{!}\text{VLocation} ( l )
  \;\to\;
  v
}{\text{(E-Deref 1)}}
$$

Se a localização l não existir na memória, ocorre erro de execução análogo a `EvaluationError("Localização inválida")`. Se e não for uma localização, também ocorre erro.
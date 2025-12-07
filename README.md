#   `L2`
Implementação da linguagem `L2` em OCaml.
`L2` é uma extensão do Cálculo Lambda tipado sobre expressões numéricas e algumas construções imperativas.

---

## Execução
Para executar o programa, faça no terminal:

```sh
[make clean];
make;
./main
```

---

##  Sobre o trabalho
Neste trabalho, foi implementada a inferência estática de tipos e avaliação de termos para a linguagel `L_2`.
A sintaxe de termos e valores pode ser encontrada `docs/termos.md`, e a sintaxe de tipos pode ser encontrada `docs/tipos.md`.
Em `avaliação.md` são descritos alguns detalhes da avaliação, assim como em `inferência_de_tipos.md` é descrita a inferência de tipos.

- `src/Constructions.ml`        :    estruturas usadas para a inferência estática de tipos (ambiente de tipos) e para a avaliação de termos (memória e tabela de símbolos).
- `src/Representations.ml`      :    representações em formato de string para termos, valores, tipos, ambiente de tipos, memória, regras de inferência de tipos e avaliação de termos.
- `src/Types.ml`                :    tipos da linguagem `L2`.
- `src/Terms.ml`                :    sintaxe de termos e de valores sobre `L2`.
- `src/TypeInference.ml`        :    inferência estática de tipos para `L2`.
- `src/Evaluation.ml`           :    avaliação de termos para `L2`.
- `src/Interpreter.ml`          :    "interpretador" de brinquedo de `L2` com inferência estática de tipos e avaliação de termos.
- `src/Testing.ml`              :   alguns termos para testes
- `src/main.ml`                 :   driver principal para chamar o interpretador.

Foi implementado um *interpretador de brinquedo* para, dado um termo, imprimir
    1.  seu tipo, e as regras de inferência de tipos usadas para tipá-lo; e
    2.  o seu valor, e as regras de avaliação usadas para avaliá-lo.

```ocaml
let interpret (e : term) : unit =
  let (t, t_rules) = infer e in
  match t with
  | ErrorType s -> print_endline s
  | t ->
    begin
      section "Type Inference";
      print_just_typeinfer e t t_rules;
      section "Evaluation";
        begin
          let (valor, tabela_de_simbolos, memoria, regras_de_avaliacao) = stepn e [] [] 100 in 
            print_endline "------------------------------------------";
            print_endline (ast_of_term e);
            print_endline (string_of_term e);
            print_endline "------------------------------------------";
            
            print_endline (" : " ^ string_of_tipo t);
            print_endline (string_of_type_inference t_rules);
            print_endline "------------------------------------------";
            print_endline (" = " ^ string_of_value valor);
            print_endline (string_of_evaluation regras_de_avaliacao);
            print_endline "------------------------------------------";
            print_endline (string_of_mem memoria);
          end
    end
```

O interpretador assume um limite `100` de passos de avaliação. Este parâmetro é passado para a função `stepn`, que avalia `n` passos de um termo `e`, e pode ser alterado.

O driver é bastante simples, apenas mapeando uma lista de termos para inferência e avaliação ao interpretador, e imprimindo os resultados.

```ocaml
let () =                            
  List.iteri
    (fun i e ->
        print_endline ("teste " ^ string_of_int (i + 1));
        interpret e;
        print_endline "")
    testes
```

onde `testes` deve ser uma lista de termos.

---

##  Instruções
### Definir um novo termo
Armado com a sintaxe de termos em `docs/termos.md` e `src/Terms.ml`. Abaixo, implementaremos um termo diretamente e uma função que, dados dois inteiros, produz um termo de $L_2$.

```ocaml
(** em `src/Testing.ml` *)

(**
  let x : int = 10 in
  let y : int = 0 in 
    (while ( x > y ) do
      x := !x - 1;
      y := !y + 1
    );
    
    !y)
*)
let counter : term = 
  Let ("x", Int, Integer 10,
    Let ("y", Int, Integer 0,
      Sequence (
        While (
          BinaryOperation (Gt, Dereference (Identifier "x"), Dereference (Identifier "y")),
          Sequence (
            Assignment (Identifier "x", 
              BinaryOperation (Sub, Dereference (Identifier "x"), Integer 1)),
            Assignment (Identifier "y",
              BinaryOperation (Add, Dereference (Identifier "y"), Integer 1))
          )
        ),
        Dereference (Identifier "y")
      )
    )
  )

(**
  let dividendo : Int = a in
  let divisor   : Int = b in
  let resto     : Int Ref = dividendo in
    (while ( resto >= divisor ) do
      resto := !resto - divisor
    );
    !resto
*)
let modulo (a: int) (b: int) : term =
  Let ("dividendo", Int, a,
    Let ("divisor", Int, b,
      Let ("resto", Reference Int, New (Identifier "dividendo"),
        Sequence (
          While (
            BinaryOperation (Geq, Dereference (Identifier "resto"), Identifier "divisor"),
            Assignment (
              Identifier "resto",
              BinaryOperation (Sub, 
                Dereference (Identifier "resto"), 
                Identifier "divisor"
              )
            )
          ),
          Dereference (Identifier "resto")
        )
      )
    )
  )
```

### Executar o interpretador
Agora podemos definir uma lista de testes

```ml
(* em `src/Testing.ml` *)


(** testes para avaliação e inferência de tipos *)
let testes = [
  counter;
  modulo (Integer 10) (Integer 3);
] in ...
```

e chamá-la em nosso interpretador, para que este imprima os resultados da **inferência estática de tipo** e da **avaliação** dos nossos termos testes.

```ocaml
(* em `src/main.ml` *)

let () =                            
  List.iteri
    (fun i e ->
        print_endline ("Teste " ^ string_of_int (i + 1));
        interpret e;
        print_endline "")
    testes
```

a interpretação pode ser visualizada em `results.txt`.

---
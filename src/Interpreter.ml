(**
    src/Interpreter.ml

    High-level interpreter for the L2 language.
    Orchestrates:
      - type inference
      - evaluation
      - pretty-printing
*)

open Types
open Terms
open Constructions
open Representations
open Evaluation
open TypeInference


(* -------------------------------------------------------------------------- *)
(* Helpers for printing                                                       *)
(* -------------------------------------------------------------------------- *)

let section title =
  print_endline ("--- " ^ title ^ " ---")

let print_line s = print_endline ("  " ^ s)
let print_raw  s = print_endline s


(* -------------------------------------------------------------------------- *)
(* Pretty printing for a full interpretation                                  *)
(* -------------------------------------------------------------------------- *)

let print_interpretation
      (e        : term)
      (t        : tipo)
      (rules    : type_inference)
      (v        : value)
      (mem      : memory)
      (ev_trace : evaluation)
    : unit =
begin
  section "Source";
  print_raw (string_of_term e);

  section "AST";
  print_raw (ast_of_term e);

  section "Type";
  print_raw (": " ^ string_of_tipo t);

  if rules <> [] then begin
    section "Type Derivation";
    print_raw (string_of_type_inference rules)
  end;

  section "Result Value";
  print_raw ("= " ^ string_of_value v);

  section "Evaluation Trace";
  print_raw (string_of_evaluation ev_trace);

  if mem <> [] then begin
    section "Final Memory";
    print_raw (string_of_mem mem)
  end;

  print_endline "------------------------------------------"
end


(* -------------------------------------------------------------------------- *)
(* Type inference only: pretty output                                         *)
(* -------------------------------------------------------------------------- *)

let print_just_typeinfer (e : term) (t : tipo) (rules : type_inference) : unit =
begin
  section "Source";
  print_raw (string_of_term e);

  section "AST";
  print_raw (ast_of_term e);

  section "Type";
  print_raw (": " ^ string_of_tipo t);

  if rules <> [] then begin
    section "Type Derivation";
    print_raw (string_of_type_inference rules)
  end;

  print_endline "------------------------------------------"
end



(**
    Interpretador para `L_2`
    
    O interpretador é apenas uma função que tentará
      tentar fazer a inferência de tipo de um termo,
      imprimir seu tipo e as regras de derivação deste;
      
      tentar fazer a avaliação de um termo,
      imprimir seu valor e as regras de avaliação deste;
      
      e terminar.
      
    A função de avaliação (`stepn`, isto é, dê n passos na avaliação
    de um termo etc.) retorna um tipo resultado. Enquanto for Ok na
    função `stepn`, esta está avaliando e produzindo termos. Quando
    ocorre um Error em `stepn`, é porque a avaliação chegou em uma
    avaliação presa, stuck. Então, para o interpretador, a função
    `stepn` DEVE e sempre (?) retornará um Error. Este Error contém
  
    (valor, tabela de símbolos, memória, regras de avaliação)
    
    que são impressos em tela, etc.
*)
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
          match stepn e [] [] 100 [] with
          | Error (v, table, mem, rules) ->
            (** valor ou erro produzido na avaliação *)
            print_endline (string_of_evaluation rules);
            print_endline (ast_of_term e);
            print_endline (string_of_term e);
            print_endline (" = " ^ string_of_value v);
    
          | Ok (e, table, mem, rules) ->
            print_endline (string_of_evaluation rules);

          end
    end

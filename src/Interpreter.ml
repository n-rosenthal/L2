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


(* -------------------------------------------------------------------------- *)
(*Full interpretation: performs type inference then evaluation                *)
(* -------------------------------------------------------------------------- *)

let interpret (e : term) : unit =
  let (t, t_rules) = infer e in
  match t with
  | ErrorType msg ->
      (* Type error: don't try to evaluate *)
      section "Type Error";
      print_raw msg;
      print_line "Evaluation skipped.";
      print_endline "------------------------------------------"

      | _ ->
        (* Successfully typed: evaluate term *)
        begin
          match multi_step e [] 100 with
          | Error msg ->
              (* dynamic evaluation error *)
              section "Evaluation Error";
              print_raw msg;
              print_endline "------------------------------------------"
    
          | Ok (final_t, mem, ev_trace) ->
              (* convert final term to value and print everything *)
              let v = value_of_term final_t in (match v with
                | None ->
                    (* runtime error value returned (EvaluationError) *)
                    section "Runtime Error";
                    print_endline "------------------------------------------"
                | Some v ->
                    print_interpretation e t t_rules v mem ev_trace
              )
        end
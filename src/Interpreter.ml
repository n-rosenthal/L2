(**
    `src/Interpreter.ml`
    
    Interpretador para a linguagem `L2`
*)

open Evaluation
open TypeInference
open Terms
open Types

(** dado um termo `e`, interpreta `e`, retornando uma tripla `(valor, tipo, memoria)`*)
let interpret (e: term) : (value * tipo * memory) = (match evaluate e [] with
    | Some (v, mem) -> (v, typeinfer e [], mem)
    | None -> (Error "RuntimeError", typeinfer e [], []))
;;

  (** interpretador para L2 *)
let interpreter (e: term) : unit = (match interpret e with
    | (Error s, _, _) -> (
        print_endline (ast_of_term e);
        print_endline (string_of_term e);
        print_endline ("\t :" ^ string_of_tipo (typeinfer e []));
        print_endline ("\t não é possível avaliar o termo em L2");
    )
    
    | (v, t, mem) -> (
        print_endline (ast_of_term e);
        print_endline (string_of_term e);
        print_endline ("\t :" ^ string_of_tipo t);
        print_endline ("\t = " ^ string_of_value v);
        print_endline ("\t in " ^ string_of_mem mem))
    )
;;

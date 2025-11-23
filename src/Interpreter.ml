(**
    `src/Interpreter.ml`
    
    Interpretador para a linguagem `L2`
*)

open Evaluation
open TypeInference
open Terms
open Types

let interpret (e: term) : unit = (
    let infer (e: term) : string = match typeinfer e [] with
        | Ok t -> string_of_tipo t
        | Error exn -> string_of_exn exn
    in
    print_endline (string_of_term e);
    print_endline (ast_of_term e);
    print_endline (infer e);
    print_endline (string_of_term (evaluate e));
    print_endline "---\n"
);

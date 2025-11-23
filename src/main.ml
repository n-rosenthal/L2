open Interpreter
open Terms

let testes = [
  Boolean true;
  Boolean false;
  Conditional (Boolean true, Boolean true, Boolean false);
  Conditional (Boolean false, Boolean true, Boolean false);

  (** if(e1, e2, e3) quando e1 !: Bool *)
  Conditional (Integer 1, Boolean true, Boolean false);

  (** if(e1, e2, e3) quando t2 <> t3 *)
  Conditional (Boolean true, Integer 1, Boolean false);

  (*  inteiros *)
  Integer (1); Integer (-1); Integer 0;

  (** sequência: e1; e2
      se (e1 ->* v1 & v1 : Unit) então e1; e2 -> e2 *)
  Sequence (Unit, Integer 1);
  Sequence (Conditional(Boolean true, Unit, Unit), Integer 1);

];;

let binary_operations = [
  (** op. bin. aritméticas *)
  BinaryOperation (Add, Integer 1, Integer 2);
  BinaryOperation (Add, Integer (-1), Integer (-2));
  BinaryOperation (Sub, Integer 1, Integer 2);
  BinaryOperation (Sub, Integer (-1), Integer (-2));
  BinaryOperation (Mul, Integer 1, Integer 2);
  BinaryOperation (Mul, Integer (-1), Integer (-2));

  (** op. bin. aritmética: divisão *)
  BinaryOperation (Div, Integer 4, Integer 2);  (** divisão inteira ok *)
  BinaryOperation (Div, Integer 5, Integer 2);  (** divisão inteira com resto *)
  BinaryOperation (Div, Integer 1, Integer 0);  (** divisão por zero *)

  (** op. bin. relacionais aritméticas *)
  BinaryOperation (Eq, Integer 1, Integer 1);
  BinaryOperation (Eq, Integer 1, Integer 2);
  BinaryOperation (Neq, Integer 1, Integer 1);
  BinaryOperation (Neq, Integer 1, Integer 2);
  BinaryOperation (Lt, Integer 1, Integer 2);
  BinaryOperation (Lt, Integer 2, Integer 1);
  BinaryOperation (Leq, Integer 1, Integer 2);
  BinaryOperation (Leq, Integer 2, Integer 1);

  (** op. bin. lógicas *)
  BinaryOperation (And, Boolean true, Boolean true);
  BinaryOperation (And, Boolean true, Boolean false);
  BinaryOperation (And, Boolean false, Boolean true);
  BinaryOperation (And, Boolean false, Boolean false);
  BinaryOperation (Or, Boolean true, Boolean true);
  BinaryOperation (Or, Boolean true, Boolean false);
  BinaryOperation (Or, Boolean false, Boolean true);
  BinaryOperation (Or, Boolean false, Boolean false);

  (** op. bin. ERROS *)
  BinaryOperation (Add, Integer 1, Boolean true); (** int + bool *)
  BinaryOperation (Sub, Boolean false, Integer 1); (** bool - int *)
  BinaryOperation (Mul, Boolean false, Boolean true); (** bool * bool *)
  BinaryOperation (Eq, Integer 1, Boolean true); (** int == bool *)

]

let _ =
  List.iteri (fun i e -> 
                (print_int i ; print_string ".\n"); interpret e)
                (testes @ binary_operations)
;;

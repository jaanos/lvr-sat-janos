(** Abstract syntax. *)

(** Propositional logic expressions. *)
type expression =
  | Literal of string
  | Variable of string
  | True
  | False
  | Not of expression
  | And of expression * expression
  | NAnd of expression * expression
  | Or of expression * expression
  | NOr of expression * expression
  | XOr of expression * expression
  | Implies of expression * expression
  | Equiv of expression * expression
  | CNF of expression
  | DNF of expression
  | NNF of expression

type command =
  | Assignment of string * expression
  | Expression of expression
  | Horn of expression
  | SAT of expression

type node =
  | DAGAnd of dagnode * dagnode
  | DAGNot of dagnode
  | DAGLiteral of string
  | DAGTrue
  | DAGFalse
and dagnode = DAGNode of node * dagnode list ref * bool option ref

(** Conversion of expressions to strings. *)
let string_of_expression e =
  let rec to_str n e =
    let (m, str) = match e with
      | Literal p           ->  (6, p)
      | Variable x          ->  (6, x)
      | True                ->  (6, "T")
      | False               ->  (6, "F")
      | Not e               ->  (6, "~" ^ (to_str 6 e))
      | And (e1, e2)        ->  (5, (to_str 5 e1) ^ " /\\ " ^ (to_str 6 e2))
      | Or (e1, e2)         ->  (4, (to_str 4 e1) ^ " \\/ " ^ (to_str 5 e2))
      | XOr (e1, e2)        ->  (3, (to_str 3 e1) ^ " + " ^ (to_str 4 e2))
      | NAnd (e1, e2)       ->  (2, (to_str 3 e1) ^ " /|\\ " ^ (to_str 3 e2))
      | NOr (e1, e2)        ->  (2, (to_str 3 e1) ^ " \\|/ " ^ (to_str 3 e2))
      | Implies (e1, e2)    ->  (1, (to_str 2 e1) ^ " => " ^ (to_str 1 e2))
      | Equiv (e1, e2)      ->  (0, (to_str 0 e1) ^ " <=> " ^ (to_str 1 e2))
      | CNF e               ->  (0, to_str n e)
      | DNF e               ->  (0, to_str n e)
      | NNF e               ->  (0, to_str n e)
    in
      if m < n then "(" ^ str ^ ")" else str
  in
    to_str (-1) e

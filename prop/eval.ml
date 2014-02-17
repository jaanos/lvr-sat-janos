(** Evaluation of expressions, given as big step semantics. *)

open Syntax

let rec nnf env = function
  | Variable x  -> (
    match env with
      | [] -> failwith ("Variable " ^ x ^ " not defined")
      | (v, e)::t -> if x = v then nnf env e else nnf t (Variable x)
    )
  | And (e1, e2)            -> And (nnf env e1, nnf env e2)
  | Or (e1, e2)             -> Or (nnf env e1, nnf env e2)
  | XOr (e1, e2)            -> And (Or (nnf env e1, nnf env e2), Or (nnf env (Not e1), nnf env (Not e2)))
  | NAnd (e1, e2)           -> Or (nnf env (Not e1), nnf env (Not e2))
  | NOr (e1, e2)            -> And (nnf env (Not e1), nnf env (Not e2))
  | Implies (e1, e2)        -> Or (nnf env (Not e1), nnf env e2)
  | Equiv (e1, e2)          -> And (Or (nnf env e1, nnf env (Not e2)), Or (nnf env (Not e1), nnf env e2))
  | Not (And (e1, e2))      -> Or (nnf env (Not e1), nnf env (Not e2))
  | Not (Or (e1, e2))       -> And (nnf env (Not e1), nnf env (Not e2))
  | Not (XOr (e1, e2))      -> And (Or (nnf env e1, nnf env (Not e2)), Or (nnf env (Not e1), nnf env e2))
  | Not (NAnd (e1, e2))     -> And (nnf env e1, nnf env e2)
  | Not (NOr (e1, e2))      -> Or (nnf env e1, nnf env e2)
  | Not (Implies (e1, e2))  -> And (nnf env e1, nnf env (Not e2))
  | Not (Equiv (e1, e2))    -> And (Or (nnf env e1, nnf env e2), Or (nnf env (Not e1), nnf env (Not e2)))
  | Not (Not e)             -> nnf env e
  | e                       -> e

let cnf env e =
    let rec align = function
      | And (e1, And (f1, f2))  -> align (And (align (And (e1, f1)), f2))
      | e                       -> e
    in let rec distr e1 e2 = match (e1, e2) with
      | (And (f1, f2), e2)  -> And (distr f1 e2, distr f2 e2)
      | (e1, And (f1, f2))  -> And (distr e1 f2, distr e2 f2)
      | (e1, Or (f1, f2))   -> distr (distr e1 f1) f2
      | (e1, e2)            -> Or (e1, e2)
    in let rec cnf = function
      | And (e1, e2)    -> And (cnf e1, cnf e2)
      | Or (e1, e2)     -> distr (cnf e1) (cnf e2)
      | e               -> e
    in align (cnf (nnf env e))


let dnf env e = e

let rec eval env = function
  | Variable x  -> (
    match env with
      | [] -> failwith ("Variable " ^ x ^ " not defined")
      | (v, e)::t -> if x = v then e else eval t (Variable x)
    )
  | CNF e       -> cnf env e
  | DNF e       -> dnf env e
  | NNF e       -> nnf env e
  | e           -> e
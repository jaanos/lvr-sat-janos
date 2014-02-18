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
  | Not False               -> True
  | Not True                -> False
  | NNF e                   -> nnf env e
  | CNF e                   -> cnf env e
  | DNF e                   -> dnf env e
  | e                       -> e

and cnf env e =
    let rec elim pos neg = function
      | And (e1, e2)    -> 
        let f1 = elim pos neg e1 in
        let f2 = elim pos neg e2 in (
          match (f1, f2) with
            | (False, e2)   -> False
            | (e1, False)   -> False
            | (True, e2)    -> f2
            | (e1, True)    -> f1
            | (e1, e2)      -> And (f1, f2)
        )
      | Or (e1, True)   -> True
      | Or (e1, False)  -> elim pos neg e1
      | Or (e1, Not e2) -> if List.exists ((=) e2) neg then elim pos neg e1
                               else if List.exists ((=) e2) pos then True
                               else (
                                match elim pos (e2 :: neg) e1 with
                                  | True    -> True
                                  | False   -> Not e2
                                  | f1      -> Or(f1, Not e2)
                               )
      | Or (e1, e2)     -> if List.exists ((=) e2) pos then elim pos neg e1
                               else if List.exists ((=) e2) neg then True
                               else (
                                match elim (e2 :: pos) neg e1 with
                                  | True    -> True
                                  | False   -> e2
                                  | f1      -> Or(f1, e2)
                               )
      | Not e               -> if List.exists ((=) e) neg then False
                               else if List.exists ((=) e) pos then True
                               else Not e
      | e                   -> if List.exists ((=) e) pos then False
                               else if List.exists ((=) e) neg then True
                               else e
    in let rec align = function
      | And (e1, And (f1, f2))  -> align (And (And (e1, f1), f2))
      | And (e1, e2)            -> And (align e1, e2)
      | e                       -> e
    in let rec distr e1 e2 = match (e1, e2) with
      | (And (f1, f2), e2)  -> And (distr f1 e2, distr f2 e2)
      | (e1, And (f1, f2))  -> And (distr e1 f1, distr e1 f2)
      | (e1, Or (f1, f2))   -> distr (Or (e1, f1)) f2
      | (Or (f1, f2), e2)   -> Or (distr f1 f2, e2)
      | (e1, e2)            -> Or (e1, e2)
    in let rec cnf = function
      | And (e1, e2)    -> And (cnf e1, cnf e2)
      | Or (e1, e2)     -> distr (cnf e1) (cnf e2)
      | NNF e           -> cnf e
      | CNF e           -> cnf e
      | DNF e           -> dnf env e
      | e               -> e
    in elim [] [] (align (cnf (nnf env e)))

and dnf env e =
    let rec elim pos neg = function
      | Or (e1, e2)         -> 
        let f1 = elim pos neg e1 in
        let f2 = elim pos neg e2 in (
          match (f1, f2) with
            | (True, e2)    -> True
            | (e1, True)    -> True
            | (False, e2)   -> f2
            | (e1, False)   -> f1
            | (e1, e2)      -> Or (f1, f2)
        )
      | And (e1, False)     -> False
      | And (e1, True)      -> elim pos neg e1
      | And (e1, Not e2)    -> if List.exists ((=) e2) neg then elim pos neg e1
                               else if List.exists ((=) e2) pos then False
                               else (
                                match elim pos (e2 :: neg) e1 with
                                  | False   -> False
                                  | True    -> Not e2
                                  | f1      -> And(f1, Not e2)
                               )
      | And (e1, e2)        -> if List.exists ((=) e2) pos then elim pos neg e1
                               else if List.exists ((=) e2) neg then False
                               else (
                                match elim (e2 :: pos) neg e1 with
                                  | False   -> False
                                  | True    -> e2
                                  | f1      -> And(f1, e2)
                               )
      | Not e               -> if List.exists ((=) e) neg then True
                               else if List.exists ((=) e) pos then False
                               else Not e
      | e                   -> if List.exists ((=) e) pos then True
                               else if List.exists ((=) e) neg then False
                               else e
    in let rec align = function
      | Or (e1, Or (f1, f2))    -> align (Or (Or (e1, f1), f2))
      | Or (e1, e2)             -> Or (align e1, e2)
      | e                       -> e
    in let rec distr e1 e2 = match (e1, e2) with
      | (Or (f1, f2), e2)   -> Or (distr f1 e2, distr f2 e2)
      | (e1, Or (f1, f2))   -> Or (distr e1 f1, distr e1 f2)
      | (e1, And (f1, f2))  -> distr (And (e1, f1)) f2
      | (And (f1, f2), e2)  -> And (distr f1 f2, e2)
      | (e1, e2)            -> And (e1, e2)
    in let rec dnf = function
      | Or (e1, e2)     -> Or (dnf e1, dnf e2)
      | And (e1, e2)    -> distr (dnf e1) (dnf e2)
      | NNF e           -> dnf e
      | CNF e           -> cnf env e
      | DNF e           -> dnf e
      | e               -> e
    in elim [] [] (align (dnf (nnf env e)))

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

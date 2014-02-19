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

let horn env e =
    let rec hornA = function
      | And (e1, e2)    -> (hornA e1) @ (hornA e2)
      | True            -> []
      | False           -> [False]
      | Literal p       -> [Literal p]
      | _               -> failwith "Not a Horn formula"
    in let hornC e = function
      | True        -> ([], True)
      | False       -> (hornA e, False)
      | Literal p   -> (hornA e, Literal p)
      | _           -> failwith "Not a Horn formula"
    in let rec hornH = function
      | And (e1, e2)        -> (hornH e1) @ (hornH e2)
      | Implies (e1, e2)    -> [hornC e1 e2]
      | Not e               -> [(hornA e, False)]
      | True                -> []
      | False               -> [([], False)]
      | Literal p           -> [([], Literal p)]
      | _                   -> failwith "Not a Horn formula"
    in let rec mark m c =
        let rec all_marked = function
          | []              -> true
          | False::_        -> false
          | (Literal p)::t  -> if List.exists ((=) p) m
                                then all_marked t else false
          | _               -> failwith "Internal error"
        in function
          | []                  -> Some m
          | (_, True)::t        -> mark m c t
          | (ps, False)::t      -> if all_marked ps
                                    then None else mark m ((ps, False)::c) t
          | (ps, Literal p)::t  -> if all_marked ps
                                    then mark (if List.exists ((=) p) m then m else p::m) [] (t@c)
                                    else mark m ((ps, Literal p)::c) t
          | _                   -> failwith "Internal error"
    in mark [] [] (hornH (eval env e))

let rec negand = function
  | And (e1, e2)            -> And (negand e1, negand e2)
  | Or (e1, e2)             -> Not (And (negand (Not e1), negand (Not e2)))
  | XOr (e1, e2)            -> And (Not (And (negand (Not e1), negand (Not e2))), Not (And (negand e1, negand e2)))
  | NAnd (e1, e2)           -> Not (And (negand e1, negand e2))
  | NOr (e1, e2)            -> And (negand (Not e1), negand (Not e2))
  | Implies (e1, e2)        -> Not (And (negand e1, negand (Not e2)))
  | Equiv (e1, e2)          -> And (Not (And (negand (Not e1), negand e2)), Not (And (negand e1, negand (Not e2))))
  | Not (And (e1, e2))      -> Not (And (negand e1, negand e2))
  | Not (Or (e1, e2))       -> And (negand (Not e1), negand (Not e2))
  | Not (XOr (e1, e2))      -> And (Not (And (negand (Not e1), negand e2)), Not (And (negand e1, negand (Not e2))))
  | Not (NAnd (e1, e2))     -> And (negand e1, negand e2)
  | Not (NOr (e1, e2))      -> Not (And (negand (Not e1), negand (Not e2)))
  | Not (Implies (e1, e2))  -> And (negand e1, negand (Not e2))
  | Not (Equiv (e1, e2))    -> And (Not (And (negand (Not e1), negand (Not e2))), Not (And (negand e1, negand e2)))
  | Not (Not e)             -> negand e
  | Not False               -> True
  | Not True                -> False
  | NNF e                   -> negand e
  | CNF e                   -> negand e
  | DNF e                   -> negand e
  | e                       -> e

let rec dag d e = try List.assoc e !d
    with Not_found -> let n = match e with
      | And (e1, e2)    -> let (DAGNode (_, p1, _)) as d1 = dag d e1
                        in let (DAGNode (_, p2, _)) as d2 = dag d e2
                        in let n = DAGNode (DAGAnd (d1, d2), ref [], ref None)
                        in p1 := n :: !p1;
                           p2 := n :: !p2;
                           n
      | Not e           -> let (DAGNode (_, p1, _)) as d1 = dag d e
                        in let n = DAGNode (DAGNot d1, ref [], ref None)
                        in p1 := n :: !p1;
                           n
      | Literal p       -> DAGNode (DAGLiteral p, ref [], ref None)
      | True            -> DAGNode (DAGTrue, ref [], ref (Some true))
      | False           -> DAGNode (DAGFalse, ref [], ref (Some false))
      | _               -> failwith "Internal error"
    in d := (e, n) :: !d; n

let rec valuate ((DAGNode (n, p, v)) as d) w =
    let rec update_parents p = match (p, w) with
      | ([], _)                                         -> true
      | (((DAGNode (DAGAnd _, _, _)) as pn)::t, false)  -> valuate pn false
                                                        && update_parents t
      | (((DAGNode (DAGAnd (n1, n2), _, {contents = Some false})))::t, true) ->
        valuate (if d == n1 then n2 else n1) false && update_parents t
      | (((DAGNode (DAGNot _, _, _)) as pn)::t, _)      -> valuate pn (not w)
                                                        && update_parents t
      | (_::t, _)                                       -> update_parents t        
    in if !v <> None then !v = Some w else (
    v := Some w; (match n with
      | DAGAnd (n1, n2) -> (match (w, n1, n2) with
          | (true, _, _)    -> valuate n1 true && valuate n2 true
          | (false, DAGNode (_, _, {contents = Some true}), _)
                            -> valuate n2 false
          | (false, _, DAGNode (_, _, {contents = Some true}))
                            -> valuate n1 false
          | _               -> true)
      | DAGNot n1       -> valuate n1 (not w)
      | _               -> true)
      && update_parents !p)

let sat env e =
    let d = ref []
    in let rec collect = function
      | []                                      -> ([], [])
      | (_, (DAGNode (DAGLiteral p, _, v)))::t  -> (
        match !v with
          | None    -> failwith "Satisfiability undecided"
          | Some b  -> let (ps, ns) = collect t
                    in if b then (p::ps, ns) else (ps, p::ns)
      )
      | _::t                                    -> collect t
    in let na = negand (eval env e)
    in print_endline (string_of_expression na);
    if valuate (dag d na) true
    then Some (collect !d) else None
    
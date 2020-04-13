(** The type of binary operators. *)
type bop = 
  | Add
  | Mult

(** The type of the abstract syntax tree (AST). *)
type expr =
  | Var of string
  | Int of int
  | Binop of bop * expr * expr
  | Let of string * expr * expr

let rec subst e v x =
  match e with 
  | Var y -> if y = x then v else e
  | Int _ -> e
  | Binop (bop, e1, e2) -> Binop (bop, subst e1 v x, subst e2 v x)
  | Let (y, e1, e2) -> let e1' = subst e1 v x in 
    if x = y then Let (y, e1', e2) else Let (y, e1', subst e2 v x)


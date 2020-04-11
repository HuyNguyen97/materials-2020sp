(** The type of binary operators. *)
type bop = 
  | Add
  | Mult
  | Sub

(** The type of the abstract syntax tree (AST). *)
type expr =
  | Int of int
  | Binop of bop * expr * expr
  | IfZero of expr * expr * expr

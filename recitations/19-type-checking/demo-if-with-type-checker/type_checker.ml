open Ast 

type typ = TInt | TBool 

module type Context = sig 
  type t 
  val empty : t
  val lookup : t -> string -> typ 
  val extend : t -> string -> typ -> t 
end 

module Context : Context = struct 
  type t = (string * typ) list
  let empty = []
  let lookup ctx x = 
    try List.assoc x ctx 
    with Not_found -> failwith "Unbound variable"
  let extend ctx x ty = (x, ty) :: ctx 
end 

open Context

let rec typeof ctx = function
  | Int _ -> TInt
  | Bool _ -> TBool 
  | Var x -> lookup ctx x
  | Binop (bop, e1, e2) -> typeof_bop ctx bop e1 e2
  | Let (x, e1, e2) -> typeof_let ctx x e1 e2 
  | If (e1, e2, e3) -> typeof_if ctx e1 e2 e3

and typeof_bop ctx bop e1 e2 =
  let t1, t2 = typeof ctx e1, typeof ctx e2 in 
  match bop, t1, t2 with 
  | Add, TInt, TInt -> TInt
  | Mult, TInt, TInt -> TInt
  | Leq, TInt, TInt -> TBool
  | _ -> failwith "Operator and operand type mismatch"

and typeof_if ctx e1 e2 e3 = 
  match typeof ctx e1, typeof ctx e2, typeof ctx e3 with 
  | TBool, t2, t3 ->
    if t2 = t3 then t2 else failwith "Both branches of if must have same type"
  | _ -> failwith "Guard of if must be a bool"

and typeof_let ctx x e1 e2 =
  let t1 = typeof ctx e1 in 
  let ctx' = extend ctx x t1 in 
  typeof ctx' e2

let typecheck e = 
  ignore (typeof empty e)







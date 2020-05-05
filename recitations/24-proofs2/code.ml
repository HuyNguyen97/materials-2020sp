module type MyStack = sig
  type 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val peek : 'a t -> 'a
  val push : 'a -> 'a t -> 'a t
  val pop : 'a t -> 'a t
end

module ListStack : MyStack = struct
  type 'a t = 'a list
  let empty = []
  let is_empty s = s = []
  let peek = List.hd
  let push = List.cons
  let pop = List.tl
end

module type Queue = sig
  type 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val front : 'a t -> 'a
  val enq : 'a -> 'a t -> 'a t
  val deq : 'a t -> 'a t
end

module ListQueue : Queue = struct
  type 'a t = 'a list
  let empty = []
  let is_empty q = q = []
  let front = List.hd
  let enq x s = s @ [x]
  let deq = List.tl
end

module TwoListQueue : Queue = struct
  (* AF: (f, b) represents the queue f @ (List.rev b).
     RI: given (f, b), if f is empty then b is empty. *)
  type 'a t = 'a list * 'a list

  let empty = [], []

  let is_empty (f, _) = 
    f = []

  let enq x (f, b) =
    if f = [] then [x], []
    else f, x :: b

  let front (f, _) = 
    List.hd f 

  let deq (f, b) =
    match List.tl f with
    | [] -> List.rev b, []
    | t -> t, b
end

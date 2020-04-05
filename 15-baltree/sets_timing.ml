module type Set = sig
  (* ['a t] is the type of sets whose elements have type ['a]. *)
  type 'a t

  (* [empty] is the empty set *)
  val empty : 'a t

  (* [insert x s] is the set ${x} \union s$. *)
  val insert : 'a -> 'a t -> 'a t

  (* [mem x s] is whether $x \in s$. *)
  val mem : 'a -> 'a t -> bool

  (* [of_list lst] is the smallest set containing all the elements of [lst]. *)
  val of_list : 'a list -> 'a t

  (* [elements s] is the list containing the same elements as [s]. *)
  val elements : 'a t -> 'a list
end

(* [from i j l] is the list containing the integers from
 *   [i] to [j], inclusive, followed by the list [l].
 * example:  [from 1 3 [0] = [1;2;3;0]] *)
let rec from i j l =
  if i>j then l
  else from i (j-1) (j::l)

(* [i -- j] is the list containing the integers from
 *   [i] to [j], inclusive.
*)
let (--) i j =
  from i j []

(* [generic_of_list] is a helper function that creates a set by
 * adding all the elements of [lst] to [empty] by using [insert]. *)
let generic_of_list lst empty insert =
  List.fold_left (fun s x -> insert x s) empty lst

module ListSet = struct
  (* AF: [x1; ...; xn] represents the set {x1, ..., xn}.
   * RI: no duplicates. *)
  type 'a t = 'a list

  let empty = []

  let mem = List.mem

  let insert x s =
    if mem x s then s else x::s

  let of_list lst =
    generic_of_list lst empty insert

  let elements s = s
end

module BstSet = struct
  (* AF:  [Leaf] represents the empty set.  [Node (l, v, r)] represents
   *   the set $AF(l) \union {v} \union AF(r)$. *)
  (* RI:  for every [Node (l, v, r)], all the values in [l] are strictly
   *   less than [v], and all the values in [r] are strictly greater
   *   than [v]. *)
  type 'a t = Leaf | Node of 'a t * 'a * 'a t

  let empty = Leaf

  let rec mem x = function
    | Leaf -> false
    | Node (l, v, r) ->
      if x < v then mem x l
      else if x > v then mem x r
      else true

  let rec insert x = function
    | Leaf -> Node (Leaf, x, Leaf)
    | Node (l, v, r) ->
      if x < v then Node(insert x l, v, r )
      else if x > v then Node(l, v, insert x r)
      else Node(l, x, r)

  let of_list lst =
    generic_of_list lst empty insert

  let rec elements = function
    | Leaf -> []
    | Node (l, v, r) -> (elements l) @ [v] @ (elements r)
end

(* [linear_bst n] is a BST constructed by inserting 1..n in linear order *)
let linear_bst n =
  BstSet.of_list (1--n)

(* [rand_bst n] is a BST constructed by inserting 1..n in a random order *)
let rand_bst n =
  BstSet.of_list (QCheck.Gen.generate1 (QCheck.Gen.shuffle_l (1--n)))

module RbSet = struct

  type color = Red | Blk

  (* AF:  [Leaf] represents the empty set.  [Node (_, l, v, r)] represents
   *   the set $AF(l) \union {v} \union AF(r)$. *)
  (* RI:
   * 1. for every [Node (l, v, r)], all the values in [l] are strictly
   *    less than [v], and all the values in [r] are strictly greater
   *    than [v].
   * 2. no Red Node has a Red child.
   * 3. every path from the root to a leaf has the same number of
        Blk nodes. *)
  type 'a t = Leaf | Node of (color * 'a t * 'a * 'a t)

  let empty = Leaf

  let rec mem x = function
    | Leaf -> false
    | Node (_, l, v, r) ->
      if  x < v then mem x l
      else if x > v then mem x r
      else true

  (* [balance (col, l, v, r)] implements the four possible rotations
   * that could be necessary to balance a node and restore the
   * RI clause about Red nodes. *)
  let balance = function
    | (Blk, Node (Red, Node (Red, a, x, b), y, c), z, d)
    | (Blk, Node (Red, a, x, Node (Red, b, y, c)), z, d)
    | (Blk, a, x, Node (Red, Node (Red, b, y, c), z, d))
    | (Blk, a, x, Node (Red, b, y, Node (Red, c, z, d)))
      -> Node (Red, Node (Blk, a, x, b), y, Node (Blk, c, z, d))
    | t -> Node t

  (* [insert' x t] finds the right place to insert [x] in [t], and
   * rebalances the resulting tree *)
  let rec insert' x = function
    | Leaf -> Node(Red, Leaf, x, Leaf)  (* color new node red *)
    | Node (col, l, v, r) ->
      if x < v then balance (col, (insert' x l), v, r)
      else if x > v then balance (col, l, v, (insert' x r))
      else Node (col, l, x, r)

  let insert x s =
    match insert' x s with
    | Node (_, l, v, r) -> Node(Blk, l, v, r)  (* color root black *)
    | Leaf -> failwith "impossible"

  let of_list lst =
    generic_of_list lst empty insert

  let rec elements = function
    | Leaf -> []
    | Node (_, l, v, r) -> (elements l) @ [v] @ (elements r)
end

(* [time f x] is [y, t], where [y = f x] and [t] is the amount of time that
 * it takes [f x] to evaluate *)
let time f x =
  let before = Unix.gettimeofday () in
  let y = f x in
  let after = Unix.gettimeofday () in
  y, after -. before

module MakeSetTimer (S:Set) = struct
  (* [insert_all lst s] inserts all the elements of [lst] into [s]. *)
  let insert_all lst s =
    List.fold_left (fun s x -> S.insert x s) s lst

  (* [mem_all lst s] checks whether each element of [lst] is in [s]. *)
  let mem_all lst s =
    List.iter (fun x -> ignore (S.mem x s)) lst

  (* [test_lsts ins_lst mem_lst] inserts all the elements of [ins_lst] into
   * a set, then tests for membership of all the elements of [mem_lst] in that
   * set, returning a pair [t_ins, t_mem], which is the amount of time it took
   * to insert and the amount of time it took to check membership. *)
  let test_lsts ins_lst mem_lst =
    let s, t_ins = time (insert_all ins_lst) S.empty in
    let _, t_mem = time (mem_all mem_lst) s in
    t_ins, t_mem

  (* [test_inorder n] tests how long it takes to insert [n] elements then check
   * for membership of [2*n] elements, all in linear order. *)
  let test_inorder n =
    "inorder", test_lsts (1--n) (1--(2*n))

  (* [test_rand n] tests how long it takes to insert [n] elements in random
   * order then check for membership of [2*n] elements in linear order. *)
  let test_rand n =
    "rand",
    test_lsts
      (QCheck.Gen.generate1 (QCheck.Gen.shuffle_l (1--n)))
      (1--(2*n))

  (* [test n] tests the linear and random workloads for [n] elements *)
  let test n =
    [test_inorder n; test_rand n]

end

module ListTimer = MakeSetTimer(ListSet)
module BstTimer = MakeSetTimer(BstSet)
module RbTimer = MakeSetTimer(RbSet)

(* [test n] tests the linear and random workloads for the three
 * set implementations *)
let test n =
  [
    "List", ListTimer.test n;
    "Bst", BstTimer.test n;
    "Rb", RbTimer.test n;
  ]

type color = Red | Black
type 'a t = Leaf | Node of color * 'a t * 'a * 'a t

let rec mem tree x : bool = match tree with
   | Leaf -> false
   | Node (_, l, v, r) -> 
    if x < v then mem l v else if x > v then mem r v else true

let rec balance_root tree : 'a t = match tree with
    | Node (Black, Node (Red, Node (Red, a, x, b), y, c), z, d)
    | Node (Black, Node (Red, a, x, Node (Red, b, y, c)), z, d)
    | Node (Black, a, x, Node (Red, Node (Red, b, y, c), z, d))
    | Node (Black, a, x, Node (Red, b, y, Node (Red, c, z, d)))
      -> Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
    | _ -> tree

let rec insert_helper tree x = match tree with
  | Leaf -> Node (Red, Leaf, x, Leaf) 
  | Node (c, l, v, r) as n ->
  if x < v then balance_root (Node (c, insert_helper l x, v, r))
  else if x > v then balance_root (Node (c, l, v, insert_helper r x))
  else n

let insert x s = 
  match insert_helper x s with
  | Leaf -> failwith "Impossible because insert_helper never returns Leaf"
  | Node (_, l, v, r) -> Node (Black, l, v, r)
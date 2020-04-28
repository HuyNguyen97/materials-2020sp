let rec from n = n :: (from (n + 1));;

let nats = from 0;;

let f1 = failwith "oops";;

let f2 = fun () -> failwith "oops";;

f2 ();;

type 'a stream = Cons of ('a * (unit -> 'a stream));;

let rec from n = Cons (n, fun () -> from (n + 1));;

let nats = from 0;;

let hd (Cons (v, t)) = v;;

let tl (Cons (v, t)) = t ();;

let rec take n (Cons (v, t)) = if n = 0 then [] else v :: take (n - 1) (t ());;

take 10 nats;;

let rec square (Cons (v, t)) = Cons (v * v, fun () -> square (t ()));;

take 10 (square nats);;

let rec sum s1 s2 = Cons ((hd s1) + (hd s2), fun () -> sum (tl s1) (tl s2));;

take 10 (sum nats (square nats));;

let rec map f s = Cons (f (hd s), fun () -> map f (tl s));;

take 10 (map (fun x -> x + 1) nats);;

let rec map2 op s1 s2 = Cons (op (hd s1) (hd s2), fun () -> map2 op (tl s1) (tl s2));;

let rec sum' s1 s2 = map2 (+) s1 s2;;

take 10 (sum' nats nats);;

let rec nats = Cons (0, fun () -> map (fun x -> x + 1) nats);;

take 10 nats;;

let rec fibs = 
Cons (1, fun () ->
Cons (1, fun () -> 
sum fibs (tl fibs)));;

take 10 fibs;;

take 30 fibs;; (* slow *)

module type MyLazy = sig 
type 'a lazy_t
val force: 'a lazy_t -> 'a 
end;;

let l = lazy (take 30 fibs);;

Lazy.force l;;

Lazy.force l;;

type 'a lazystream = Cons of ('a * 'a lazystream lazy_t);;

let hd (Cons (v, t)) = v;;

let tl (Cons (v, t)) = Lazy.force t;;

let rec take n (Cons (v, t)) = if n = 0 then [] else v :: take (n - 1) (Lazy.force t);;

let rec sum s1 s2 = Cons ((hd s1) + (hd s2), lazy (sum (tl s1) (tl s2)));;

let rec fibs = 
  Cons (1, lazy (
    Cons (1, lazy (
      sum fibs (tl fibs)))));;

take 30 fibs;;

take 1000 fibs;;








(* Next: cool definition of nats, fib, fib being slow,
semantics of laziness, import lazy_stream,
show that fib is now fast.
that's it! Maybe say a little about why lazy is needed/
eager vs lazy evaluation, haskell*)
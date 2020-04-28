(* Core functionality for generic stream type. *)
module type BasicStream = sig
  type 'a d 
  type 'a stream = Cons of 'a * 'a stream d
  val make : 'a -> (unit -> 'a stream) -> 'a stream
  val hd : 'a stream -> 'a
  val tl : 'a stream -> 'a stream 
end

(* Generic stream type. *)
module type Stream = sig 
  include BasicStream
  val take : int -> 'a stream -> 'a list
  val map : ('a -> 'b) -> 'a stream -> 'b stream
  val map2 : ('a -> 'b -> 'c) -> 'a stream -> 'b stream -> 'c stream
end

(* Represents possible strategies for delaying the evaluation of expressions *)
module type DelayedEvaluation = sig 
  type 'a d
  val wrap : (unit -> 'a) -> 'a d
  val unwrap : 'a d -> 'a
end

module BasicStream (D : DelayedEvaluation) : (BasicStream with type 'a d = 'a D.d) = struct
  type 'a d = 'a D.d
  type 'a stream = Cons of 'a * 'a stream d
  let make v t = Cons (v, D.wrap t)
  let hd (Cons (v, t)) = v
  let tl (Cons (v, t)) = D.unwrap t
end 

(* Delayed evaluation using thunks. *)
module ThunkEvaluation : (DelayedEvaluation with type 'a d = unit -> 'a) = struct
  type 'a d = unit -> 'a
  let wrap t = t
  let unwrap t = t ()
end

(* Delayed evaluation using OCaml laziness *)
module OCamlLazyEvaluation : (DelayedEvaluation with type 'a d = 'a lazy_t) = struct
  type 'a d = 'a lazy_t
  let wrap t = lazy (t ())
  let unwrap l = Lazy.force l
end 

module BasicThunkStream = BasicStream (ThunkEvaluation)
module BasicLazyStream = BasicStream (OCamlLazyEvaluation)

module Stream (B : BasicStream) : (Stream with type 'a d = 'a B.d) = struct
  include B
  (* Deduplicated code, using hd, tl, and make! *)
  let rec take n s = if n <= 0 then [] else hd s :: take (n - 1) (tl s)
  let rec map f s = make (f (hd s)) (fun () -> map f (tl s))
  let rec map2 op s1 s2 = make (op (hd s1) (hd s2)) (fun () -> map2 op (tl s1) (tl s2))
end

module ThunkStream = Stream (BasicThunkStream)
module LazyStream = Stream (BasicLazyStream)

(* Can use the same code for both *)
open LazyStream
let rec from n = make n (fun () -> from (n + 1))
let nats = from 0
open ThunkStream
let rec from n = make n (fun () -> from (n + 1))
let nats = from 0

(* However, for technical reasons, when making recursive definitions, you need to use the Cons type constructor, so the above pattern doesn't quite work. *)
open LazyStream
let rec nats = Cons (0, lazy (map (fun x -> x + 1) nats))
open ThunkStream
let rec nats = Cons (0, fun () -> map (fun x -> x + 1) nats)

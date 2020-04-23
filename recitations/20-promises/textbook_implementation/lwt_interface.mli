module type Lwt = sig
  (* [Sleep] means pending.  [Return] means resolved.
     [Fail] means rejected. *)
  type 'a state = Sleep | Return of 'a | Fail of exn

  (* a [t] is a promise *)
  type 'a t

  (* a [u] is a resolver *)
  type 'a u

  val state : 'a t -> 'a state

  (* [wakeup] means [resolve] *)
  val wakeup : 'a u -> 'a -> unit

  (* [wakeup_exn] means [reject] *)
  val wakeup_exn : 'a u -> exn -> unit

  (* [wait] means [make] *)
  val wait : unit -> 'a t * 'a u

  val return : 'a -> 'a t
end
(** A signature for Lwt-style promises, with better names *)
type 'a state = Pending | Resolved of 'a | Rejected of exn
type 'a promise
type 'a resolver

(** [make ()] is a new promise and resolver. The promise is pending. *)
val make : unit -> 'a promise * 'a resolver

(** [return x] is a new promise that is already resolved with value [x]. *)
val return : 'a -> 'a promise

(** [state p] is the state of the promise *)
val state : 'a promise -> 'a state

(** [resolve r x] resolves the promise [p] associated with [r]
    with value [x], meaning that [state p] will become 
    [Resolved x].
    Requires:  [p] is pending. *)
val resolve : 'a resolver -> 'a -> unit

(** [reject r x] rejects the promise [p] associated with [r]
    with exception [x], meaning that [state p] will become
    [Rejected x].
    Requires:  [p] is pending. *)
val reject : 'a resolver -> exn -> unit
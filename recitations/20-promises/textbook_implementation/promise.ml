type 'a state = Pending | Resolved of 'a | Rejected of exn
    
type 'a promise = 'a state ref

type 'a resolver = 'a promise

let make () : 'a promise * 'a resolver = 
  let p = ref Pending in
  p, p

let state (p : 'a promise) = !p

let write_once (p : 'a resolver) (s : 'a state) = 
  if !p = Pending
  then p := s
  else invalid_arg "cannot write twice"

let resolve (r : 'a resolver) (x : 'a) = write_once r (Resolved x)
let reject (r : 'a resolver) (x : exn) = write_once r (Rejected x)

let return x = ref (Resolved x)



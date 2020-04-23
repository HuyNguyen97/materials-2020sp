open Lwt
open Lwt_io

let _ = ignore (bind (read_line stdin) printl); printl "done";;
open Lwt
open Lwt_io
open Lwt_main

let p = read_line stdin

let _ = printl "done"

let _ = bind p printl

let _ = Lwt_main.run p
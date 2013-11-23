open Translater

type result =
  | TRUE
  | FALSE
  | UNKNOWN

let verify ft main_node =
  let _ = translate ft main_node in
  UNKNOWN

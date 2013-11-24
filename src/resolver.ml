open Translater
open Prover


let verify ft main_node =
  let (eq, ok_ident) = translate ft main_node in
  prover eq ok_ident

open Translater
open Prover


let verify ft main_node =
  let _(*(eq, ok_ident)*) = translate ft main_node in
  UNKNOWN(*prover eq ok_ident*)

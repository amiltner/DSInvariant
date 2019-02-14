open Verifiers
open Base

type var = string * Type.t

type 'a func = {
  args : var list ;
  name : string ;
  expr : (module Verifier with type expr = 'a) -> 'a list -> 'a ;
  return : Type.t ;
}

type 'a t = {
  insert_func     : 'a func ;
  delete_func     : 'a func ;
  lookup_func     : 'a func ;
  post_func       : 'a func ;

  constants       : Value.t list ;
  synth_variables : var list     ;
}

open Base
open Verifiers

type var = string * Type.t

type 'a func = verifier:(module Verifier) -> 'a -> 'a -> 'a

type 'a t = {
  precond_func    : 'a func ;
  delete_func     : 'a func  ;
  empty_func      : 'a func  ;
  insert_func     : 'a func  ;
  lookup_func     : 'a func  ;
  post_func       : 'a func  ;

  constants       : Value.t list ;
  synth_variables : var list     ;
}

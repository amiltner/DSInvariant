open Core

open Lang
open Exceptions
open Utils

type t = {
  neg_tests : Value.t list ;
  pos_tests : Value.t list ;
} [@@deriving show]

let create_positive pos_tests : t =
  { pos_tests = List.dedup_and_sort ~compare:Value.compare pos_tests
  ; neg_tests = [] }

let add_pos_test ~(testbed : t) (test : Value.t) : t =
  if List.exists testbed.pos_tests ~f:(( = ) test) then
    testbed
  else if List.exists testbed.neg_tests ~f:(( = ) test) then
    raise
      (Ambiguous_Test ("New POS test ("
                       ^ Value.show test ^ ") already already exists in NEG set!"))
  else { testbed with
         pos_tests = test :: testbed.pos_tests }

let add_neg_test ~(testbed : t) (test : Value.t) : t =
  if List.exists testbed.neg_tests ~f:(( = ) test) then
    testbed
  else if List.exists testbed.pos_tests ~f:(( = ) test) then
    raise
      (Ambiguous_Test ("New NEG test ("
                       ^ Value.show test ^ ") already already exists in POS set!"))
  else { testbed with
         neg_tests = test :: testbed.neg_tests }
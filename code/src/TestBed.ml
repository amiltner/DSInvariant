open MyStdlib
open Lang
open Exceptions
open Utils

type desc = string
type 'a feature = 'a -> bool
type 'a with_desc = 'a * desc
type ('a, 'b) postcond = 'a -> ('b, exn) Result.t -> bool

type ('a, 'b) _t = {
  features : 'a feature with_desc list ;
  neg_tests : ('a * (bool list lazy_t)) list ;
  pos_tests : ('a * (bool list lazy_t)) list ;
}

type t = (Value.t, Value.t) _t

let show x =
  let show_value_list = string_of_list Value.show in
  string_of_pair
    show_value_list
    show_value_list
    (List.map ~f:fst x.pos_tests,List.map ~f:fst x.neg_tests)


let to_string (x:t) =
  "negs:"^(string_of_list (Value.show % fst) x.neg_tests)^
  "pos:"^(string_of_list (Value.show % fst) x.pos_tests)

let compute_feature_value (test : 'a) (feature : 'a feature with_desc) : bool =
  try (fst feature) test with _ -> false
  [@@inline always]

let compute_feature_vector (test : 'a) (features : 'a feature with_desc list)
                           : bool list =
  List.map ~f:(compute_feature_value test) features
  [@@inline always]

let create_positive ?(features = []) pos_tests : t =
  { features
  ; pos_tests = List.map pos_tests ~f:(fun t -> (t, lazy (compute_feature_vector t features)))
  ; neg_tests = []
  }

(*let split_tests ~f tests =
  List.fold ~init:([],[]) tests
    ~f:(fun (l1,l2) t -> try if post t (Result.try_with (fun () -> f t))
                             then (t :: l1, l2) else (l1, t :: l2)
                         with IgnoreTest -> (l1, l2)
                            | _ -> (l1, t :: l2))*)

let add_pos_test ~(testbed : t) (test : Value.t) : t option =
  if List.exists testbed.pos_tests ~f:(fun (pt, _) -> pt = test) then
    None
  else if List.exists testbed.neg_tests ~f:(fun (nt, _) -> nt = test) then
    raise
      (Ambiguous_Test ("New POS test ("
                       ^ Value.show test ^ ") already already exists in NEG set!"))
  else
    Some
      {
        testbed with
        pos_tests =
          (test ,lazy (compute_feature_vector test testbed.features))
          :: testbed.pos_tests
      }

let add_neg_test ~(testbed : t) (test : Value.t) : t option =
  if List.exists testbed.neg_tests ~f:(fun (pt, _) -> pt = test) then
    None
  else if List.exists testbed.pos_tests ~f:(fun (nt, _) -> nt = test) then
    raise
      (Ambiguous_Test ("New NEG test ("
                       ^ Value.show test ^ ") already already exists in POS set!"))
  else
    Some
      {
        testbed with
        neg_tests =
          (test ,lazy (compute_feature_vector test testbed.features))
          :: testbed.neg_tests
      }

let add_pos_test_allow_dups ~(testbed : t) (test : Value.t) : t =
  begin match add_pos_test ~testbed test with
    | None -> testbed
    | Some testbed -> testbed
  end

let add_pos_test_disallow_dups ~(testbed : t) (test : Value.t) : t =
  Option.value_exn (add_pos_test ~testbed test)

let add_neg_test_allow_dups ~(testbed : t) (test : Value.t) : t =
  begin match add_neg_test ~testbed test with
    | None -> testbed
    | Some testbed -> testbed
  end

let add_neg_test_disallow_dups ~(testbed : t) (test : Value.t) : t =
  Option.value_exn (add_neg_test ~testbed test)

let add_feature ~(testbed : t) (feature : 'a feature with_desc) : t =
  let add_to_fv (t, old_fv) =
    (t, lazy ((compute_feature_value t feature) :: (Lazy.force old_fv)))
  in {
       features = feature :: testbed.features ;
       pos_tests = List.map testbed.pos_tests ~f:add_to_fv ;
       neg_tests = List.map testbed.neg_tests ~f:add_to_fv ;
     }

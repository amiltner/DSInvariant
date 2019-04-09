open MyStdlib

open Exceptions
open Utils

type desc = string
type 'a feature = 'a -> bool
type 'a with_desc = 'a * desc
type ('a, 'b) postcond = 'a -> ('b, exn) Result.t -> bool

type ('a, 'b) _t = {
  farg_names : string list ;
  farg_types : Type.t list ;
  features : 'a feature with_desc list ;
  neg_tests : ('a * (bool list lazy_t)) list ;
  pos_tests : ('a * (bool list lazy_t)) list ;
  post : ('a, 'b) postcond ;
}

type t = (Value.t list, Value.t) _t

let to_string (x:t) =
  "negs:"^(string_of_list ((string_of_list Value.to_string) % fst) x.neg_tests)^
  "pos:"^(string_of_list ((string_of_list Value.to_string) % fst) x.pos_tests)

let compute_feature_value (test : 'a) (feature : 'a feature with_desc) : bool =
  try (fst feature) test with _ -> false
  [@@inline always]

let compute_feature_vector (test : 'a) (features : 'a feature with_desc list)
                           : bool list =
  List.map ~f:(compute_feature_value test) features
  [@@inline always]

let create_positive ~args ~post ?(features = []) pos_tests : t =
  { post ; features
  ; farg_names = List.map args ~f:fst
  ; farg_types = List.map args ~f:snd
  ; pos_tests = List.map pos_tests ~f:(fun t -> (t, lazy (compute_feature_vector t features)))
  ; neg_tests = []
  }

let split_tests ~f ~post tests =
  List.fold ~init:([],[]) tests
    ~f:(fun (l1,l2) t -> try if post t (Result.try_with (fun () -> f t))
                             then (t :: l1, l2) else (l1, t :: l2)
                         with IgnoreTest -> (l1, l2)
                            | _ -> (l1, t :: l2))

let add_pos_test ~(testbed : t) (test : Value.t list) : t =
  if List.exists testbed.pos_tests ~f:(fun (pt, _) -> pt = test)
  then (*raise (Duplicate_Test ("New POS test (" ^ (String.concat ~sep:"," testbed.farg_names)
                             ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                             ^ "), already exists in POS set!"))*) testbed
  else if List.exists testbed.neg_tests ~f:(fun (nt, _) -> nt = test)
  then raise (Ambiguous_Test ("New POS test (" ^ (String.concat ~sep:"," testbed.farg_names)
                             ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                             ^ ") already exists in NEG set!"))
  else
    {
      testbed with
      pos_tests =
        (test ,lazy (compute_feature_vector test testbed.features))
        :: testbed.pos_tests
    }

let add_neg_tests ~(testbed : t) (test : Value.t list) : t =
  if List.exists testbed.neg_tests ~f:(fun (nt, _) -> nt = test)
  then (*raise (Duplicate_Test ("New NEG test (" ^ (String.concat ~sep:"," testbed.farg_names)
                             ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                             ^ ") already exists in NEG set!"))*) testbed
  else if List.exists testbed.pos_tests ~f:(fun (pt, _) -> pt = test)
  then raise (Ambiguous_Test ("New NEG test (" ^ (String.concat ~sep:"," testbed.farg_names)
                             ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                             ^ ") already exists in POS set!"))
  else
    {
      testbed with
      neg_tests = (test ,lazy (compute_feature_vector test testbed.features))
                  :: testbed.neg_tests
    }

let add_feature ~(testbed : t) (feature : 'a feature with_desc) : t =
  let add_to_fv (t, old_fv) =
    (t, lazy ((compute_feature_value t feature) :: (Lazy.force old_fv)))
  in { testbed with
       features = feature :: testbed.features ;
       pos_tests = List.map testbed.pos_tests ~f:add_to_fv ;
       neg_tests = List.map testbed.neg_tests ~f:add_to_fv ;
     }

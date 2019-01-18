open Core_kernel

open BFL
open Exceptions
open Utils

type 'a conflict = {
  pos : 'a list ;
  neg : 'a list ;
  fvec : bool list ;
}

type config = {
  for_BFL : BFL.config ;

  synth_logic : Logic.t ;
  disable_synth : bool ;
  max_conflict_group_size : int ;
}

let base_max_conflict_group_size = 32

let default_config : config = {
  for_BFL = BFL.default_config ;

  synth_logic = Logic.of_string "LIA" ;
  disable_synth = false ;
  max_conflict_group_size = base_max_conflict_group_size ;
}

let conflictingTests (testbed : TestBed.t) : 'a conflict list =
  let make_f_vecs = List.map ~f:(fun (t, fvec) -> (t, Lazy.force fvec)) in
  let make_groups tests =
    List.group tests ~break:(fun (_, fv1) (_, fv2) -> fv1 <> fv2)
  in let (p_groups, n_groups) = (make_groups (make_f_vecs testbed.pos_tests),
                                 make_groups (make_f_vecs testbed.neg_tests))
  in List.(filter_map
       p_groups
       ~f:(fun [@warning "-8"] (((_, pfv) :: _) as ptests) ->
             match find n_groups ~f:(fun ((_, nfv) :: _) -> nfv = pfv) with
             | None -> None
             | Some ntests -> Some { pos = map ~f:fst ptests
                                   ; neg = map ~f:fst ntests
                                   ; fvec = pfv }))

let synthFeature ?(consts = []) ~(testbed : TestBed.t) ~(logic : Logic.t)
                 (conflict_group : Value.t list conflict) : Value.t list TestBed.feature TestBed.with_desc =
  let open Synthesizer in
  let result = solve consts {
    logic ;
    arg_names = testbed.farg_names ;
    inputs = (let all_inputs = conflict_group.pos @ conflict_group.neg in
      List.mapi testbed.farg_names
                ~f:(fun i _ -> Array.of_list List.(map all_inputs ~f:(fun l -> nth_exn l i))));
    outputs = Array.of_list ((List.map conflict_group.pos ~f:(fun _ -> Value.Bool true))
                            @ (List.map conflict_group.neg ~f:(fun _ -> Value.Bool false)))
  } in ((fun values -> try Value.equal (result.func values) (Value.Bool true) with _ -> false),
        (if result.constraints = [] then result.string
         else "(and " ^ result.string ^ (String.concat ~sep:" " result.constraints) ^ ")"))

let resolveAConflict ?(conf = default_config) ?(consts = []) ~(testbed : TestBed.t)
                     (conflict_group' : Value.t list conflict)
                     : Value.t list TestBed.feature TestBed.with_desc =
  let group_size = List.((length conflict_group'.pos) + (length conflict_group'.neg))
  in let group_size = group_size * (conf.synth_logic.conflict_group_size_multiplier)
  in let conflict_group = if group_size < conf.max_conflict_group_size then conflict_group'
                   else { conflict_group' with
                          pos = List.take conflict_group'.pos (conf.max_conflict_group_size / 2);
                          neg = List.take conflict_group'.neg (conf.max_conflict_group_size / 2)
                        }
  in Log.debug (lazy ("Invoking synthesizer with "
                      ^ (conf.synth_logic.name) ^ " logic."
                      ^ (Log.indented_sep 0) ^ "Conflict group ("
                      ^ (List.to_string_map2 testbed.farg_names testbed.farg_types ~sep:" , "
                           ~f:(fun n t -> n ^ " :" ^ (Type.to_string t))) ^ "):" ^ (Log.indented_sep 2)
          ^ "POS (" ^ (Int.to_string (List.length conflict_group.pos)) ^ "):" ^ (Log.indented_sep 4)
                      ^ (List.to_string_map conflict_group.pos ~sep:(Log.indented_sep 4)
                           ~f:(fun vl -> "(" ^ (List.to_string_map vl ~f:Value.to_string ~sep:" , ") ^ ")")) ^ (Log.indented_sep 2)
          ^ "NEG (" ^ (Int.to_string (List.length conflict_group.neg)) ^ "):" ^ (Log.indented_sep 4)
                      ^ (List.to_string_map conflict_group.neg ~sep:(Log.indented_sep 4)
                           ~f:(fun vl -> "(" ^ (List.to_string_map vl ~f:Value.to_string ~sep:" , ") ^ ")"))))
   ; let new_feature = synthFeature conflict_group ~logic:conf.synth_logic ~consts ~testbed
     in Log.debug (lazy ("Synthesized feature:" ^ (Log.indented_sep 4) ^ (snd new_feature)))
      ; new_feature

let rec resolveSomeConflicts ?(conf = default_config) ?(consts = []) ~(testbed : TestBed.t)
                             (conflict_groups : Value.t list conflict list)
                             : Value.t list TestBed.feature TestBed.with_desc option =
  if conflict_groups = [] then None
  else try Some (resolveAConflict (List.hd_exn conflict_groups) ~conf ~consts ~testbed)
       with e -> Log.error (lazy ((Exn.to_string e) ^ (Printexc.get_backtrace ())))
               ; resolveSomeConflicts (List.tl_exn conflict_groups) ~conf ~consts ~testbed

let rec augmentFeatures ?(conf = default_config) ?(consts = []) (testbed : TestBed.t) : TestBed.t =
  let conflict_groups = conflictingTests testbed
  in if conflict_groups = [] then testbed
     else if conf.disable_synth
          then (Log.error (lazy ("CONFLICT RESOLUTION FAILED")) ; raise NoSuchFunction)
     else match resolveSomeConflicts conflict_groups ~testbed ~conf ~consts with
          | None -> Log.error (lazy ("CONFLICT RESOLUTION FAILED")) ; raise NoSuchFunction
          | Some new_feature -> augmentFeatures (TestBed.add_feature ~testbed new_feature) ~conf ~consts

let learnPreCond ?(conf = default_config) ?(consts = []) (testbed : TestBed.t)
                 : ('a TestBed.feature TestBed.with_desc) CNF.t option =
  Log.info (lazy ("New PI task with "
                  ^ (Int.to_string (List.length testbed.pos_tests))
                  ^ " POS + "
                  ^ (Int.to_string (List.length testbed.neg_tests))
                  ^ " NEG tests")) ;
  try let testbed = augmentFeatures ~conf ~consts testbed
      in let make_f_vecs = List.map ~f:(fun (_, fvec) -> Lazy.force fvec)
      in let (pos_vecs, neg_vecs) = List.(dedup_and_sort ~compare:(List.compare Bool.compare) (make_f_vecs testbed.pos_tests),
                                          dedup_and_sort ~compare:(List.compare Bool.compare) (make_f_vecs testbed.neg_tests))
      in try let cnf = learnCNF pos_vecs neg_vecs ~n:(List.length testbed.features)
                                ~conf:conf.for_BFL
             in Some (CNF.map cnf ~f:(fun i -> List.nth_exn testbed.features (i-1)))
         with ClauseEncodingError -> None
  with _ -> None

let cnf_opt_to_desc (pred : ('a TestBed.feature TestBed.with_desc) CNF.t option) : TestBed.desc =
  match pred with
  | None -> "false"
  | Some pred -> CNF.to_string pred ~stringify:snd

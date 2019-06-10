module MyRope = Rope
open Core
open Consts
open Printf
open Lang
open Sigma
open Gamma
module Rope = MyRope
open Util

(***** Type definitions {{{ *****)

(*module Output =
struct
  type t_node = ((value option) list option) list
  [@@deriving ord, show, hash]

  type t = t_node hash_consed

  let compare o1 o2 = Int.compare o1.tag o2.tag

  let table = HashConsTable.create 100000
  let hashcons = HashConsTable.hashcons hash_t_node compare_t_node table

  let create x = hashcons x
  end*)

(*type output = Output.t*)

type output = (value option option) list
[@@deriving ord, show, hash]

(*type 'a test_output_retriever = exp * exp * ('a -> bool option) * ('a -> value option option)
type 'a test = 'a -> bool list

  type 'a tests_outputs = (('a test_output_retriever)) list*)


type test_output_tree =
  | InternalNode of test_output_tree list
  | ExistantLeaf of bool * value option
  | NonexistantLeaf
[@@deriving ord, show, hash]

type test_output_tree_list = test_output_tree list
[@@deriving ord, show, hash]

type 'a tests_outputs =
  (bool * exp * exp * ('a -> test_output_tree)) list

let tests_outputs_update
    (type a)
    (type b)
    (f:a -> b)
    (tests_outputs:b tests_outputs)
  : a tests_outputs =
  List.map
    ~f:(fun (b,e1,e2,otm) ->
        (b,e1,e2, otm % f))
    tests_outputs


let to_test_output_tree_list
    (type a)
    (tests_outputs:a tests_outputs)
    (e:a)
  : test_output_tree_list =
  List.map
    ~f:(fun (_,_,_,v) -> v e)
    tests_outputs

let rec passable_test_output_tree
    (test_output_tree:test_output_tree)
  : bool =
  begin match test_output_tree with
    | InternalNode totl ->
      List.exists
        ~f:passable_test_output_tree
        totl
    | ExistantLeaf (b,_) -> b
    | NonexistantLeaf -> false
  end

let has_passing_capabilities
    (type a)
    (tests_outputs:a tests_outputs)
    (x:a)
  : bool =
  List.for_all
    ~f:passable_test_output_tree
    (to_test_output_tree_list
       tests_outputs
       x)

let to_test_io_output_tree_list
    (type a)
    (tests_outputs:a tests_outputs)
    (e:a)
  : (bool * exp * exp * test_output_tree) list =
  List.map
    ~f:(fun (b,e1,e2,v) -> (b,e1,e2,v e))
    tests_outputs

let any_updated
    (test_output_trees:test_output_tree list)
  : bool =
  let rec any_updated_tree
      (test_output_tree:test_output_tree)
    : bool =
    begin match test_output_tree with
      | InternalNode ts ->
        List.exists
          ~f:any_updated_tree
          ts
      | NonexistantLeaf -> false
      | ExistantLeaf (b,_) -> b
    end
  in
  List.exists
    ~f:any_updated_tree
    test_output_trees

let core_deduper
    (type a)
    (compare:a -> a -> int)
    (to_size:a -> int)
    (xs:a list)
  : a list =
  let sized_xs =
    List.map
      ~f:(fun x -> (x,to_size x))
      xs
  in
  let sorted_parititioned_i =
    List.sort_and_partition_with_indices
      ~cmp:(fun (e1,_) (e2,_) -> compare e1 e2)
      sized_xs
  in
  List.map
    ~f:(fun esl ->
        let ordered_by_size =
          List.sort
            ~compare:(fun ((_,s1),_) ((_,s2),_) -> Int.compare s1 s2)
            esl
        in
        let ((a,_),_) = List.hd_exn ordered_by_size in
        a)
    sorted_parititioned_i

let minimize
    (type a)
    (to_size:a -> int)
    (es:a list)
    (tests_outputs:a tests_outputs)
  : a list =
  let es_exs_tests_outputs =
    List.map
      ~f:(fun e ->
          (e,to_test_output_tree_list tests_outputs e))
      es
  in
  let productive_es_etc =
    List.filter
      ~f:(fun (_,o) -> any_updated o)
      es_exs_tests_outputs
  in
  let deduped_es =
    core_deduper
      (fun (_,o1) (_,o2) -> compare_test_output_tree_list o1 o2)
      (fun (e,_) -> to_size e)
      productive_es_etc
  in
  List.map ~f:fst deduped_es

(*let tests_outputs_to_output_full_retriever
    (type a)
    (tests_outputs:a tests_outputs)
    (e:a)
  : output =
  List.map
    ~f:(fun (_,_,_,v) -> v e)
    tests_outputs

let tests_outputs_to_tests_full_retriever
    (type a)
    (tests_outputs:a tests_outputs)
    (e:a)
  : bool list =
  List.map
    ~f:(fun (_,_,t,_) ->
        begin match t e with
          | None -> false
          | Some b -> b
        end)
    tests_outputs*)


let output_comparer = List.compare (Option.compare Lang.compare_val)
let pp_output = List.to_string ~f:(Option.value_map ~f:Pp.pp_value ~default:"None")

let split_by_minimal
    (type a)
    ~(compare:a -> a -> bool)
    (xs:a list)
  : (a list) * (a list) =
  let rec split_by_minimal_internal
      (xs:a list)
      (smalls:a list)
      (others:a list)
    : (a list) * (a list) =
    begin match xs with
      | [] -> (smalls,others)
      | h::t ->
        let contains =
          List.exists
            ~f:(fun e -> compare h e)
            smalls
        in
        if contains then
          split_by_minimal_internal
            t
            smalls
            (h::others)
        else
          let (smalls,new_large) =
            List.partition_tf
              ~f:(fun s -> not (compare s h))
              smalls
          in
          split_by_minimal_internal
            t
            (h::smalls)
            (new_large@others)
    end
  in
  split_by_minimal_internal xs [] []

let split_into_minimal_partitions
    (type a)
    ~(compare:a -> a -> bool)
    ~(total_order:a -> a -> int)
    (xs:a list)
  : ((a list) * (a list)) list =
  let rec split_into_minimal_partitions_internal
      (remaining_bigs:a list)
      (most_recent_addition:a list)
      (partition_acc:((a list) * (a list)) list)
    : ((a list) * (a list)) list =
    if List.is_empty remaining_bigs then
      partition_acc
    else
      let (littles,bigs) = split_by_minimal ~compare remaining_bigs in
      let most_recent_addition = most_recent_addition @ littles in
      split_into_minimal_partitions_internal
        bigs
        most_recent_addition
        ((most_recent_addition,bigs)::partition_acc)
  in
  let partitions =
    split_into_minimal_partitions_internal
      xs
      []
      []
  in
  List.map
    ~f:(fun (p1,p2) -> (List.sort ~compare:total_order p1, p2))
    partitions

let deduper
    (type a)
    (tests_outputs:a tests_outputs)
    (to_size:a -> int)
    (xs:a list)
  : a list =
  let es_outputs =
    List.map
      ~f:(fun x -> (x, to_size x, (to_test_output_tree_list tests_outputs x)))
      xs
  in
  let sorted_parititioned_i =
    List.sort_and_partition_with_indices
      ~cmp:(fun (_,_,e1) (_,_,e2) -> compare_test_output_tree_list e1 e2)
      es_outputs
  in
  List.map
    ~f:(fun esl ->
        let ordered_by_size =
          List.sort
            ~compare:(fun ((_,s1,_),_) ((_,s2,_),_) -> Int.compare s1 s2)
            esl
        in
        let ((a,_,_),_) = List.hd_exn ordered_by_size in
        a)
    sorted_parititioned_i

let test_performance_to_ranking
    (tp:bool list)
  : Float.t =
  let success_count =
    List.length (List.filter ~f:ident tp)
  in
  let total_count = List.length tp in
  (Float.of_int success_count) /. (Float.of_int total_count)


(* output: partial program outputs *)

(* rtree: A single node of a refinement tree.                                             *)
type rtree =
  { t                 : typ               (* Goal type that we wish to generate.          *)
  ; mutable sz        : int               (* Size of the refinement tree.                 *)
  ; g                 : Gamma.t           (* Names that are in scope.                     *)
  ; mutable timed_out : bool              (* Whether the generation process has timed out.*)
  ; mutable es        : exp list          (* Expressions that have been generated so far. *)
  ; refinements       : rnode list        (* Generated using IRefine rules.               *)
  ; mutable matches   : (rmatch list) option  (* Generated using IRefine-match rule.      *)
  ; mutable scrutinee_size : int          (* The size of scrutinees for matches.          *)
  ; forced_match      : bool              (* Generated using IRefine-match rule.      *)
  ; matches_permitted : bool
  }

and rnode =
  | SAbs   of id * arg * typ * rtree      (* IRefine-Fix.                                 *)
  | SCtor  of id * rtree                  (* IRefine-Ctor.                                *)
  | STuple of rtree list                  (* IRefine-Tuple.                               *)
  | SRcd   of rtree record                (* IRefine-Record.                              *)
  | SUnit                                 (* IRefine-Unit.                                *)

and rmatch = exp *                        (* The match scrutinee.                         *)
            (pat * rtree) list            (* The branches of the match statement.         *)

(* rtree_size: Determines the size of an rtree, which is defined as the number of rtrees  *)
(*             contained in this and child trees.                                         *)

let rec duplicate_rtree
    (t:rtree)
  : rtree =
  {
    t = t.t;
    sz = t.sz;
    g = t.g;
    timed_out = t.timed_out;
    es = t.es;
    refinements = List.map ~f:duplicate_rnode t.refinements;
    matches = Option.map ~f:(List.map ~f:duplicate_rmatch) t.matches;
    scrutinee_size = t.scrutinee_size;
    forced_match = t.forced_match;
    matches_permitted = t.matches_permitted;
  }

and duplicate_rnode
    (n:rnode)
  : rnode =
  begin match n with
    | SAbs(i,a,t,rt) ->
      SAbs(i,a,t,duplicate_rtree rt)
    | SCtor(i,t) -> SCtor(i,duplicate_rtree t)
    | STuple ts -> STuple (List.map ~f:duplicate_rtree ts)
    | SRcd _ -> failwith "ignore"
    | SUnit -> SUnit
  end

and duplicate_rmatch
    ((e,bs):rmatch)
  : rmatch =
  (e, List.map ~f:(fun (p,t) -> (p,duplicate_rtree t)) bs)

let rec rtree_size (t:rtree) : int =
  let rnode_size n =
    match n with
    | SAbs (_, _, _, t) -> rtree_size t
    | SCtor (_, t)      -> rtree_size t
    | STuple ts -> List.fold_left ~f:(fun acc t -> rtree_size t + acc) ~init:0 ts
    | SRcd ts -> List.fold_left ~f:(fun acc (_,t) -> rtree_size t + acc) ~init:0 ts
    | SUnit -> 0
  in
  let match_size ((_, ls) : rmatch) =
      List.fold_left ~f:(fun acc t -> acc + rtree_size t) ~init:0 (List.map ~f:snd ls)
  in
  let matches_size = function
    | None    -> 0
    | Some ms -> List.fold_left ~f:(fun acc m -> acc + match_size m) ~init:0 ms
  in
  List.fold_left
    ~f:(fun acc n -> acc + rnode_size n)
    ~init:(1 + matches_size t.matches)
    t.refinements

(***** }}} *****)

(***** Pretty printing {{{ *****)

type pretty_line = int * string

let print_whitespace (n:int) = (String.make (n + 1) '*') ^ "   "
let pretty_lines (lines:pretty_line list) : string list =
  List.map ~f:(fun (n, s) -> print_whitespace n ^ s) lines

let rec stringify (ss:string list) : string =
  match ss with
  | [] -> ""
  | [s] -> s
  | s :: ss -> s ^ "\n" ^ stringify ss

let stringify_rtree_matches (t:rtree) : string =
  match t.matches with
  | None    -> "growable"
  | Some ls -> sprintf "scrutinee_size = %d, #/matches = %d" t.scrutinee_size (List.length ls)

let rec build_lines_rtree (k:int) (t:rtree) : pretty_line list =
  let childlines   = List.concat_map ~f:(build_lines_rnode k t.t) t.refinements in
  let matchlines   = build_lines_matches k t.t t.matches  in
  (k, sprintf "* :: %s [E-size = %d, timed_out = %b, exp_count = %d, %s]"
     (Pp.pp_typ t.t) t.sz t.timed_out
     (List.length t.es) (stringify_rtree_matches t)) :: (matchlines @ childlines)

and build_lines_match (k:int) (tt:typ) ((e, bs):rmatch) : pretty_line list =
    let s = Printf.sprintf "match %s :: %s" (Pp.pp_exp e) (Pp.pp_typ tt) in
    (k, s) :: List.concat_map ~f:(fun (p, t) ->
      let s = sprintf "| %s ->" (Pp.pp_pat p) in
      (k+1, s) :: build_lines_rtree (k+2) t) bs

and build_lines_matches k t ms = match ms with
  | None -> []
  | Some ms -> List.concat_map ~f:(build_lines_match k t) ms

and build_lines_rnode (k:int) (tt:typ) (n:rnode) : pretty_line list =
  match n with
  | SAbs (f, (x, t1), t2, t) ->
      let s = Printf.sprintf "fix %s (%s:%s) : %s :: %s" f x (Pp.pp_typ t1) (Pp.pp_typ t2) (Pp.pp_typ tt) in
      (k, s) :: build_lines_rtree (k+1) t
  | SCtor (c, t) ->
      let s = Printf.sprintf "ctor %s :: %s" c (Pp.pp_typ tt) in
      (k, s) :: (build_lines_rtree (k+1) t)
  | STuple ts ->
      let s = Printf.sprintf "tuple :: %s" (Pp.pp_typ tt) in
      (k, s) :: List.concat_map ~f:(build_lines_rtree (k+1)) ts
  | SRcd ts ->
      let s = Printf.sprintf "record :: %s" (Pp.pp_typ tt) in
      (k, s) :: List.concat_map ~f:(fun (_,t) -> build_lines_rtree (k+1) t) ts
  | SUnit ->
      let s = Printf.sprintf "unit :: %s" (Pp.pp_typ tt) in
      [(k, s)]

let pp_rtree t = build_lines_rtree 0 t |> pretty_lines |> stringify

(***** }}} *****)

(***** Refinement tree construction {{{ *****)

type synth_branch  = id * pat * Gamma.t
type eval_val      = {
    scrut_ctor  : id;            (* The constructor that the scrutinee evaluates to.    *)
    scrut_val   : value;         (* The value that the scrutinee evalutes to (no ctor). *)
    env:env;                     (* The environment for a particular world.             *)
    goal:value;                  (* The expected outcome of the larger match statement. *)
}

(* Creates a rtree for the given synthesis problem. *)
let rec create_rtree
    (s:Sigma.t)
    (g:Gamma.t)
    (env:env)
    (t:typ)
    (matches_count:int)
    (matches_permitted:bool)
  : rtree =
  begin match Gamma.peel_nonrecursive_variant g s with
    | None ->
      { t         = t
      ; sz        = 1
      ; g         = g
      ; es        = []
      ; timed_out = false
      ; matches   = if not matches_permitted || matches_count <= 0 then None
          else Some (create_matches s g env t matches_count 1 !scrutinee_size_lim)
      ; refinements  = create_non_matches s g env t matches_count
      ; scrutinee_size = !scrutinee_size_lim
      ; forced_match = false
      ; matches_permitted = matches_permitted
      }
    | Some ((e,_),g) ->
      let m = Option.value_exn (create_match s g env t e matches_count) in
      { t         = t
      ; sz        = 1
      ; g         = g
      ; es        = []
      ; timed_out = false
      ; matches   = Some [m]
      ; refinements  = []
      ; scrutinee_size = !scrutinee_size_lim
      ; forced_match = true
      ; matches_permitted = matches_permitted
      }
  end

(***** Create refinement tree match statements {{{ *****)

(* Distributes the examples according to the constructors that e evaluates to.
 * For each examles (env, v), if env(v) ~~> C (...), then (env, v) is filed
 * under the C bucket. *)
and distribute_constraints (s:Sigma.t) (g:Gamma.t) (e:exp) : synth_branch list =
  let dt = get_base_exn (Typecheck.Typecheck.check_exp s g e) in
  Sigma.ctors dt s |> List.map ~f:begin fun (c, (c_typ, _)) ->
    (* Generate a pattern.                                                                *)
    let (p_opt, g) = match c_typ with        (* Don't create a pattern at unit type.      *)
      | TUnit -> (None, g)
      | _ -> let (p, g) = Gamma.insert_pattern c_typ g in (Some p, g)
    in
    (* Mark pattern variables as decreasing if possible.                                  *)
    let (p_opt, g) = match (p_opt, Gamma.fun_of_arg e g) with
      | (None, _) | (_, None) -> (p_opt, g)
      | (Some p, Some f) ->
        let g  = List.fold_left
              ~f:(fun g x -> Gamma.mark_as_dec_arg_of_fun x f g)
              ~init:g
              (extract_ids_from_pattern p)
        in
        (p_opt, g)
    in
      (c, (c, p_opt), g)
    end

(* Creates a single match for the given synthesis problem and scrutinee expression. *)
(* If evaluation of the potential scrutinee results in no example generated         *)
(* (because all examples resulted in bad pattern matches), then reject this         *)
(* scrutinee immediately.                                                           *)
and create_match
    (s:Sigma.t)
    (g:Gamma.t)
    (env:env)
    (t:typ)
    (e:exp)
    (matches:int)
  : rmatch option =
  (* Returns true if the given synth_branches are an adequate distribution of the       *)
    (* examples as determined by {distribute_constraints}.                                *)
    (* Every branch must have one example.                                                *)
    let branches = distribute_constraints s g e in
    let trees = List.map ~f:(fun (_, p, g) ->
      (p, create_rtree s g env t (matches-1) true)) branches
    in
  Some (e, trees) 

(* Creates match nodes for the given synthesis problem.                                   *)
and create_matches (s:Sigma.t) (g:Gamma.t) (env:env) (t:typ)
                   (matches:int)
                   (scrutinee_min:int) (scrutinee_max:int) : rmatch list =
    match t with
    | TArr _ -> []
    | _      ->
      (* Evaluate a scrutinee candidate {e} to constructors in each example world,        *)
      (* creating a corresponding eval_val for each world.                                *)

      (* Generate scrutinees of size {size} of any type.                                  *)
      let gen_scrutinees size =
          (* Generate scrutinees of size {size} and type {t}.                             *)
        let gen_scrutinees_of_type t' =
          let met = Gen.gen_metric size 1 in
          let scrut_exps = Gen.gen_eexp Timeout.unlimited s g t' met in
          let valid_exps = Rope.filter ~f:(fun e -> Gamma.contains_variant e g) scrut_exps in
          let ms = Rope.map ~f:(fun e -> create_match s g env t e matches) valid_exps in
              Rope.filter_map ~f:Fn.id ms
          in
          Rope.concat_map ~f:gen_scrutinees_of_type (Rope.of_list (Sigma.types s))
      in
      Util.rangen scrutinee_min scrutinee_max |>
      Rope.of_list                            |>
      Rope.concat_map ~f:gen_scrutinees       |>
      Rope.to_list

(***** }}} *****)

(***** Create refinement tree non-match statements {{{ *****)

(* Creates (type-directed) rtree nodes for the given synthesis problem.                   *)
and create_non_matches (s:Sigma.t) (g:Gamma.t) (env:env) (t:typ)
                       (matches:int) : rnode list =
  match t with
  | TUnit -> [SUnit]

  (* Refine constructors *)
  | TBase _ -> []

  (* Refine functions *)
  | TArr (t1, t2) ->
    let f  = Gamma.fresh_id (gen_var_base t ) g in
    let x  = Gamma.fresh_id (gen_var_base t1) (Gamma.insert f t true g) in
    let g  = Gamma.insert x t1 true g in
    [SAbs (f, (x, t1), t2, create_rtree s g env t2 matches true)]

  (* Refine tuples *)
  | TTuple ts ->
      let trees =
        List.map ~f:(fun t -> create_rtree s g env t matches false) ts
      in
      [STuple trees]

  (* Refine records *)
  | TRcd _ -> []

(***** }}} *****)

(* Grows the given refinement tree by one level of matches. *)
let rec grow_matches (s:Sigma.t) (env:env) (t:rtree) =
  if t.matches_permitted then
    begin match t.matches with
      | None ->
        let ms = create_matches s t.g env t.t 1 1 !scrutinee_size_lim in
        t.matches <- Some (ms);
        t.scrutinee_size <- !scrutinee_size_lim
      | Some ms ->
        List.iter
          ~f:(fun (_, bs) -> List.iter ~f:(fun (_, t) -> grow_matches s env t) bs)
          ms
    end;
  List.iter ~f:(grow_matches_rnode s env) t.refinements

and grow_matches_rnode (s:Sigma.t) (env:env) (n:rnode) =
  match n with
  | SAbs (_, _, _, t) -> grow_matches s env t
  | SCtor (_, t) -> grow_matches s env t
  | STuple ts -> List.iter ~f:(grow_matches s env) ts
  | SRcd ts -> List.iter ~f:(fun (_,t) -> grow_matches s env t) ts
  | SUnit -> ()

(* Grows the given refinement tree by expanding the match scrutinees by
 * size k. *)
let rec grow_scrutinees (s:Sigma.t) (env:env) (k:int) (t:rtree) =
  begin match t.matches with
  | None -> ()
  | Some ms ->
    if not t.forced_match then
      begin let min = t.scrutinee_size+1 in
        let max = t.scrutinee_size+k in
        let ms' = create_matches s t.g env t.t 1 min max in
        t.matches <- Some (ms @ ms');
        t.scrutinee_size <- max;
      end;
    List.iter
      ~f:(fun (_, bs) ->
          List.iter ~f:(fun (_, t) -> grow_scrutinees s env k t) bs)
      ms
  end;
  List.iter ~f:(grow_scrutinees_rnode s env k) t.refinements

and grow_scrutinees_rnode (s:Sigma.t) (env:env) (k:int) (n:rnode) =
  match n with
  | SAbs (_, _, _, t) -> grow_scrutinees s env k t
  | SCtor (_, t) -> grow_scrutinees s env k t
  | STuple ts -> List.iter ~f:(grow_scrutinees s env k) ts
  | SRcd ts -> List.iter ~f:(fun (_,t) -> grow_scrutinees s env k t) ts
  | SUnit -> ()

(***** }}} *****)

(***** Refinement tree manipulation {{{ *****)
let check_exp (e:exp) (env_global:env) (env_local:env) (v:value) : bool =
  try v = (Timing.record
            ~label:"update_exps::eval"
            ~action:(fun _ -> Eval.eval (env_local @ env_global) e))
  with Eval.Eval_error msg ->
    if not !incomplete_constraints_flag then begin
      incomplete_constraints_flag := true;
      eprintf "Warning: incomplete constraint set given\n%s\n" msg;
    end; false

(***** update_exps: e-guesses at each node in the rtree {{{ *****)

let rec update_exps ?short_circuit:(sc = true) (timeout:float)
                    (s:Sigma.t) (env:env) (t:rtree) =
  let do_if_no_exp (f:unit -> unit) =
    if not sc || List.length t.es = 0 then f ()
  in
  (* Update this node's expressions... *)
  do_if_no_exp (fun _ ->
    (* NOTE: only generate expressions at this node if it is at base type... *)
    begin match t.t with
    | TArr _ | TUnit | TTuple _ | TRcd _ -> ()
    | TBase _ ->
      (* ...and we have not exceeded the max eguess size nor timed out yet. *)
      if (not t.timed_out) && t.sz <= !max_eguess_size then try
        Timing.record
          ~label:"update_exps::gen"
          ~action:begin fun _ ->
            Gen.gen_eexp
              (Timeout.create timeout) s t.g t.t (Gen.gen_metric t.sz 1)
          end
        |> Rope.iter ~f:begin fun e ->
            (* TODO: probably want to short-circuit walking through gen_eexp
             * results as well... *)
            if sc then
              match t.es with
              | [] -> t.es <- e::t.es
              | _ :: _ -> ()
            else
              t.es <- e :: t.es
            end;
        t.sz <- t.sz + 1
      with
        Timeout.Timeout_exception -> begin
          do_if_verbose (fun _ ->
            Printf.printf
              "Timeout occurred while guessing, size = %d\n%!" t.sz);
          t.timed_out <- true
        end
    end);
  (* ...if we didn't update this tree's exp then recursively update it's
   * children. *)
  do_if_no_exp (fun _ -> begin
        update_exps_matches ~short_circuit:sc timeout s env t.matches;
        List.iter ~f:(update_exps_node ~short_circuit:sc timeout s env)
          t.refinements;
      end)

and update_exps_matches ?short_circuit:(sc = true) (timeout:float) (s:Sigma.t)
                        (env:env) (mopt:rmatch list option) =
  match mopt with
  | None -> ()
  | Some ms ->
      List.iter ~f:(update_exps_rmatch ~short_circuit:sc timeout s env) ms

and update_exps_rmatch ?short_circuit:(sc = true) (timeout:float)
                       (s:Sigma.t) (env:env) (m:rmatch) =
  let (_, bs) = m in
  List.iter ~f:(fun (_, t) -> update_exps ~short_circuit:sc timeout s env t) bs

and update_exps_node ?short_circuit:(sc = true) (timeout:float)
                     (s:Sigma.t) (env:env) (n:rnode) =
  begin match n with
  | SAbs (_, _, _, t) -> update_exps ~short_circuit:sc timeout s env t
  | SCtor (_, t) -> update_exps ~short_circuit:sc timeout s env t
  | STuple ts -> List.iter ~f:(update_exps ~short_circuit:sc timeout s env) ts
  | SRcd ts -> List.iter ~f:(fun (_,t) -> update_exps ~short_circuit:sc timeout s env t) ts
  | SUnit -> ()
  end

(***** }}} *****)

(***** reset_timeouts: resets the timeout flag in the rtree {{{ *****)

let rec reset_timeouts (t:rtree) = begin
  t.timed_out <- false;
  match t.matches with
  | None -> ()
  | Some ms -> begin
      List.iter ~f:(fun (_, bs) ->
          List.iter ~f:(fun (_, t) -> reset_timeouts t) bs) ms
    end;
    List.iter ~f:reset_timeouts_refinements t.refinements
end

and reset_timeouts_refinements (n:rnode) =
  match n with
  | SAbs (_, _, _, t) -> reset_timeouts t
  | SCtor (_, t) -> reset_timeouts t
  | STuple ts -> List.iter ~f:reset_timeouts ts
  | SRcd ts -> List.iter ~f:(fun (_,t) -> reset_timeouts t) ts
  | SUnit -> ()

(***** }}} *****)

(***** propogate_exps: tries to construct exps from rtree sub-children {{{ *****)

let select_tops
    (es:'a list)
    (ranking:'a -> Float.t)
    (to_size:'a -> Int.t)
  : ('a list * Float.t) option =
  let e_rank_size = List.map ~f:(fun e -> (e,(ranking e,-1 * to_size e))) es in
  let sorted_e_rank = List.sort ~compare:(fun (_,f1) (_,f2) -> (Tuple.T2.compare ~cmp1:Float.compare ~cmp2:Int.compare) f2 f1) e_rank_size in
  begin match sorted_e_rank with
    | [] -> None
    | (e,(r,_))::t ->
      if r = 1. then
        Some ([e],1.)
      else
        Some (e :: (List.map
                      ~f:fst
                      (List.take_while ~f:(fun (_,(r',_)) -> r = r') t)),r)
  end

let select_any_improve
    (es:'a list)
    (runs:('a -> bool list))
  : 'a list =
  List.filter
    ~f:(fun e ->
        List.exists
          ~f:(ident)
          (runs e))
    es


let retrieve_maxes_and_indices
    (l:'a list)
    (cmp:'a -> 'a -> int)
  : ('a * int) list =
  match l with
    | [] -> failwith "cannot"
    | h::t -> [List.foldi t ~init:(h,0)
                          ~f:(fun i (accv,acci) x ->
                              if cmp accv x < 0 then
                                (x,i+1)
                              else
                                (accv,acci))]

type pnode =
  | Node of exp * (pat * pnode) list
  | Leaf of exp

type ppath = (exp * pat) list
[@@deriving ord, show, hash]

let rec pnode_to_exp
    (p:pnode)
  : exp =
  begin match p with
    | Node (e,ppns) ->
      EMatch (e, List.map ~f:(fun (p,pn) -> (p,pnode_to_exp pn)) ppns)
    | Leaf e -> e
  end

let ppath_to_pnode
    (pp:ppath)
    (e:exp)
  : pnode =
  List.fold_right
    ~f:(fun (e,p) pn ->
        Node (e,[(p,pn)]))
    ~init:(Leaf e)
    pp

let retrieve_match_exp_exn
    (t:rtree)
  : exp =
  fst (List.hd_exn (Option.value_exn t.matches))


let rec retrieve_force_match_ppaths
    (t:rtree)
  (*(exp_finder:(exp -> output) -> (exp -> Float.t) -> rtree -> exp list)*)
  : (ppath * rtree) list =
  if t.forced_match then
    let (e,prts) = List.hd_exn (Option.value_exn t.matches) in
    List.concat_map
      ~f:(fun (p,rt) ->
          let ppess =
            retrieve_force_match_ppaths
              rt
          in
          List.map ~f:(fun (pp,t) -> ((e,p)::pp),t) ppess)
      prts
  else
    [[],t]
(*[([],exp_finder exp_to_output condition t)]*)

let rec contains_path
    (pn:pnode)
    (pp:ppath)
  : bool =
  begin match (pn,pp) with
    | (_, []) -> true
    | (Leaf _, _) -> false
    | (Node (e,ppns), (e',p')::t) ->
      if e = e' then
        List.exists
          ~f:(fun (p,pn) ->
              p = p' &&
              contains_path pn t)
          ppns
      else
        false
  end


let integrate_path
    (pp:ppath)
    (pn:pnode)
    (e_base:exp)
  : pnode option =
  let rec integrate_path_internal
      (pp:ppath)
      (pn:pnode)
    : pnode =
    begin match (pn,pp) with
      | (Node (e,ppns), (_,p)::t) ->
        let p_update =
          fun (p',pn') ->
            if p = p' then
              Some (p',integrate_path_internal t pn')
            else
              None
        in
        begin match update_first ~f:p_update ppns with
          | None -> Node (e,(p,ppath_to_pnode t e_base)::ppns)
          | Some ppns -> Node (e,ppns)
        end
      | _ -> failwith "shouldn't happen"
    end
  in
  if contains_path pn pp then
    None
  else
    Some (integrate_path_internal pp pn)

type partition_solution_cache_key = rtree * (exp * exp) list * int
type partition_solution_cache_value_component = (ppath * exp)
[@@deriving ord, show, hash]
type partition_solution_cache_value = partition_solution_cache_value_component list
type partition_solution_cache =
  (partition_solution_cache_key * partition_solution_cache_value) list

let rec any_nonforced_matches r : bool =
  let contains_itself =
    begin match r.matches with
      | None -> false
      | Some [] -> false
      | _ -> true
    end
  in
  (not r.forced_match && contains_itself)
  || List.exists ~f:any_nonforced_matches_rnode r.refinements
  || (begin match r.matches with
      | None -> false
      | Some ms -> List.exists ~f:any_nonforced_matches_rmatch ms
    end)

and any_nonforced_matches_rnode r : bool =
  begin match r with
    | SAbs(_,_,_,r) -> any_nonforced_matches r
    | SCtor(_,r) -> any_nonforced_matches r
    | STuple rs -> List.exists ~f:any_nonforced_matches rs
    | SRcd _ -> failwith "too lazy"
    | SUnit -> false
  end

and any_nonforced_matches_rmatch (_,bs) : bool =
  List.exists
    ~f:(fun (_,r) -> any_nonforced_matches r)
    bs

let rec rtree_equal r1 r2 : bool =
  r1.t = r2.t
  && r1.sz = r2.sz
  && Gamma.hash r1.g = Gamma.hash r2.g
  && r1.es = r2.es
  && List.equal ~equal:rnode_equal r1.refinements r2.refinements
  && Option.equal (List.equal ~equal:rmatch_equal) r1.matches r2.matches
  && r1.scrutinee_size = r2.scrutinee_size
  && r1.forced_match = r2.forced_match
  && r1.matches_permitted = r2.matches_permitted

and rnode_equal r1 r2 : bool =
  begin match (r1,r2) with
    | (SAbs (i1,a1,t1,rt1), SAbs (i2,a2,t2,rt2)) ->
      (compare_id i1 i2 = 0) &&
      (compare_arg a1 a2 = 0) &&
      (compare_typ t1 t2 = 0) &&
      rtree_equal rt1 rt2
    | (SCtor (i1,rt1), SCtor (i2,rt2)) ->
      (compare_id i1 i2 = 0) &&
      rtree_equal rt1 rt2
    | (STuple rts1, STuple rts2) ->
      List.equal ~equal:rtree_equal rts1 rts2
    | (SRcd _, SRcd _) -> failwith "todo"
    | (SUnit, SUnit) -> true
    | _ -> false
  end

and rmatch_equal (e1,branches1) (e2,branches2) : bool =
  (compare_exp e1 e2 = 0) &&
  List.equal ~equal:((fun (pat1,rt1) (pat2,rt2)
                     -> (compare_pat pat1 pat2 = 0) &&
                        rtree_equal rt1 rt2))
             branches1
             branches2

let solution_cache : partition_solution_cache ref = ref []

let update_solution_cache
    (t:rtree)
    (prior_pns:int)
    (prior_tests:exp tests_outputs)
    (relevant_tests:exp tests_outputs)
    (ppath_exps:(ppath * exp) list)
  : unit =
  solution_cache :=
    ((duplicate_rtree t,List.map ~f:(fun (_,i,o,_) -> (i,o)) (prior_tests@relevant_tests), prior_pns), ppath_exps)
    ::!solution_cache


let lookup_in_solution_cache
    (t:rtree)
    (prior_tests_outputs:exp tests_outputs)
    (relevant_tests_outputs:exp tests_outputs)
    (prior_pns:int)
  : partition_solution_cache_value option =
  (*let minimal_partitions_tests_outputs =
    split_into_minimal_partitions
      ~compare:(fun (e1,_,_) (e2,_,_) -> contains e1 e2)
      ~total_order:(fun (e1,_,_) (e2,_,_) -> compare_exp e1 e2)
      tests_outputs
    in*)
  let tests_outputs = prior_tests_outputs@relevant_tests_outputs in
  List.fold_left
    ~f:(fun acc_o ((t',e12s,prior_pns'),v) ->
        begin match acc_o with
          | Some _ -> acc_o
          | None ->
            if prior_pns = prior_pns' && rtree_equal t' t && (
                  (List.compare_as_multisets
                     ~cmp:(Tuple.T2.compare ~cmp1:compare_exp ~cmp2:compare_exp)
                     (List.map ~f:(fun (_,e1,e2,_) -> (e1,e2)) tests_outputs)
                     e12s) = 0) then
              Some v
            else
              None
(*
              let fst_sat_o =
                List.find
                  ~f:(fun (tests_outputs,_) ->
                        (List.compare_as_multisets
                           ~cmp:(Tuple.T2.compare ~cmp1:compare_exp ~cmp2:compare_exp)
                           (List.map ~f:(fun (e1,e2,_) -> (e1,e2)) tests_outputs)
                           e12s) = 0)
                  minimal_partitions_tests_outputs
              in
              Option.map ~f:(fun (prior,remaining) -> (v,remaining,prior)) fst_sat_o
            else
              None*)
        end)
    ~init:None
    (!solution_cache)

let rec propogate_exps ?short_circuit:(sc = true)
    (enforced_completed:bool)
    (tests_outputs:exp tests_outputs)
    (t:rtree)
    ~(search_matches:bool)
  : exp list =
  if sc && List.length t.es > 0 then
    t.es
  else
    (* NOTE: Prioritize lambdas, matches, and then constructors, in that order. *)
    let es = t.es
             @ propogate_exps_matches ~short_circuit:sc enforced_completed tests_outputs t ~search_matches
             @ List.concat_map
               ~f:(propogate_exps_node ~short_circuit:sc enforced_completed tests_outputs ~search_matches) t.refinements
    in
    (*t.es <- es;*)
    es

and propogate_exps_matches ?short_circuit:(sc = true)
    (enforced_completed:bool)
    (tests_outputs:exp tests_outputs)
    (t:rtree)
    ~(search_matches:bool)
  : exp list =
  if t.forced_match && not enforced_completed then
    propagate_enforced_matches ~short_circuit:sc tests_outputs t
  else
    match t.matches with
    | None -> []
    | Some ms ->
      if search_matches then
        begin
          let ms =
            deduper
              (tests_outputs_update fst tests_outputs)
              (size % fst)
              ms
          in
          List.concat_map
            ~f:(propogate_exps_rmatch
                 enforced_completed
                  ~short_circuit:sc
                  tests_outputs)
            ms
        end
      else
        []

and propogate_exps_rmatch ?short_circuit:(sc = true)
    (enforced_completed:bool)
    (tests_outputs:exp tests_outputs)
    (m:rmatch)
  : exp list =
  let (e, bs)  = m in
  (*let is_desired = e = EApp ((EApp (EVar "compare", EVar "n1")), EVar "n3") in*)
  (*if is_desired then print_endline "ITS HAPPENING";*)
  (*let (ps, ts) = List.unzip bs in*)
  (*print_endline (Pp.pp_exp e);
    print_endline (List.to_string ~f:(fun (p,r) -> "(" ^ Pp.pp_pat p ^ "," ^ pp_rtree r ^ ")") bs);*)
  (*print_endline "startb";
    print_endline (string_of_int (List.length bs));*)
  let nonprod_bs =
    List.map
      ~f:(fun (p,t) ->
          (*print_endline "this is slow why?";*)
          let make_match e' = EMatch(e,[(p,e')]) in
          let tests_outputs = tests_outputs_update make_match tests_outputs in
          let initial_es = propogate_exps ~short_circuit:sc enforced_completed tests_outputs ~search_matches:true t in
          (*print_endline "1";*)
          (*print_endline @$ string_of_int (List.length es);*)
          let es =
            minimize
              size
              initial_es
              tests_outputs
          in
          let nonproductive = List.length es = 0 in
          let es =
            if nonproductive then
              begin match initial_es with
                | [] -> []
                | h::_ -> [h]
              end
            else
              es
          in
          (*print_endline "abs";
          print_endline @$ string_of_int (List.length es);
            print_endline "3";*)
          (nonproductive,List.map ~f:(fun e -> (p,e)) es))
      bs
  in
  let (nonprod,bs) = List.unzip nonprod_bs in
  if List.for_all ~f:ident nonprod then
    []
  else
    let brancheses = combinations bs in
    let ans = List.map ~f:(fun bs -> EMatch(e,bs)) brancheses in

  (*let ans =
    ([[]],bs)
    List.fold_until_completion
    ~f:(fun (established_branches,bs) ->
         let make_match bs = EMatch(e,bs) in
        if bs = [] then
          Right (List.map ~f:make_match established_branches)
        else
          let integrations_rank_bos =
            List.map
              ~f:(fun pes ->
                  let full_bes =
                    cartesian_map
                      ~f:(fun pe eb -> pe::eb)
                      pes
                      established_branches
                  in
                  Option.map
                    ~f:(fun (b,v) -> (pes,b,v))
                    (select_tops
                       full_bes
                       (fun bs ->
                          test_performance_to_ranking
                            (List.map
                               ~f:(fun (_,run) -> run (make_match bs))
                               tests))
                       (size % make_match)))
              bs
          in
          let integrations_rank_bs_o = distribute_option integrations_rank_bos in
          begin match integrations_rank_bs_o with
            | None -> Right []
            | Some integrations_ranks ->
              let maxes_indices =
                retrieve_maxes_and_indices
                  integrations_ranks
                  (fun (_,_,f1) (_,_,f2) -> Float.compare f1 f2)
              in
              if List.length maxes_indices = 0 then
                failwith "unexpected"
              else if List.length maxes_indices = 1 then
                let ((_,established_branches,_),i) = List.hd_exn maxes_indices in
                (*let ((established_branches,_),i) =*)
                print_endline "BEGINIT";
                print_endline @$ string_of_int (List.length established_branches);
                let pns =
                  deduper
                    (exp_to_output % make_match)
                    (size % make_match)
                    established_branches
                in
                let (_,bs) = remove_at_index_exn bs i in
                Left (pns,bs)
              else
                failwith "TODO"
          end)
    ([[]],bs)
    in*)
  (*if is_desired then print_endline "it happened";*)
  ans
  (*let branches_o =
    List.fold_left
      ~f:(fun bss_o (p,t) ->
          begin match bss_o with
            | None -> None
            | Some bss ->
              let above_adder =
                fun e' ->
                  above_adder (EMatch (e,[(p,e')]))
              in
              let make_match e' bs = EMatch (e,(p,e')::bs) in
              let new_condition =
                fun e ->
                  Option.value_exn
                    (List.max_elt
                       ~compare:Float.compare
                       (List.map
                          ~f:(fun bs -> condition (make_match e bs))
                          bss))
              in
              print_endline "hi there";
              print_endline (pp_rtree t);
              let t_es = propogate_exps ~short_circuit:sc above_adder new_condition deduper t in
              let pe = List.map ~f:(fun e -> (p,e)) t_es in
              print_endline (string_of_int (List.length pe));
              print_endline (string_of_int (List.length bss));
              let non_projected = Util.cartesian_map ~f:List.cons pe bss in
              print_endline "why?";
              let ans = select_tops
                  non_projected
                  (fun bs -> condition (EMatch (e,bs))) in
              Option.map ~f:fst ans
          end)
      ~init:(Some [[]])
      bs
  in
    print_endline "endb";
  begin match branches_o with
    | None -> []
    | Some branches ->
      List.map ~f:(fun bs -> EMatch (e, bs)) branches
    end*)

and propogate_exps_node
    ?short_circuit:(sc = true)
    (enforced_completed:bool)
    (tests_outputs:exp tests_outputs)
    ~(search_matches:bool)
    (n:rnode)
  : exp list =
  match n with
  | SUnit -> [EUnit]

  | SAbs (f, x, ty, t) ->
    let e_transformer = fun e -> EFix (f, x, ty, e) in
    let tests_outputs = tests_outputs_update e_transformer tests_outputs in
    List.map
      ~f:e_transformer
      (propogate_exps
         ~short_circuit:sc
         enforced_completed
         tests_outputs
         ~search_matches
         t)

  | SCtor (c, t) ->
    propogate_exps ~short_circuit:sc enforced_completed tests_outputs ~search_matches t |> List.map ~f:(fun e -> ECtor (c, e))

  | STuple ts ->
    List.map ~f:(propogate_exps ~short_circuit:sc enforced_completed tests_outputs ~search_matches) ts
    |> Util.combinations
    |> List.map ~f:(fun es -> ETuple es)

  | SRcd ts ->
    List.map ~f:(fun (l,t) ->
        List.map ~f:(fun e -> (l,e)) (propogate_exps ~short_circuit:sc enforced_completed tests_outputs ~search_matches t)) ts
    |> Util.combinations
    |> List.map ~f:(fun es -> ERcd es)

and propagate_enforced_matches
    ?short_circuit:(sc = true)
    (tests_outputs:exp tests_outputs)
    (t:rtree) : exp list =
  let ppaths =
    retrieve_force_match_ppaths
      t
      (*(fun above_adder condition ->
         propogate_exps
           ~short_circuit:sc
           above_adder
           condition)*)
  in
  let pns =
  List.fold_until_completion
    ~f:(fun (pns,tests_outputs,prior_tests) ->
        if List.length tests_outputs = 0 then
          Right pns
        else
          let passing =
              List.filter
                ~f:(fun pn ->
                    has_passing_capabilities
                      (tests_outputs_update pnode_to_exp tests_outputs)
                      pn)
                pns
          in
          let standard_calc () =
            let (relevant_tests_outputs,next_tests_outputs) =
                split_by_minimal
                  ~compare:(fun (_,e1,_,_) (_,e2,_,_) -> contains e1 e2)
                  tests_outputs
              in
              let all_tests_outputs =
                relevant_tests_outputs
                @
                (List.map
                   ~f:(fun (_,e,r,t) -> (false,e,r,t))
                   next_tests_outputs)
              in
              let pns_size = List.length pns in

              let possible_branches =
                begin match lookup_in_solution_cache t prior_tests relevant_tests_outputs pns_size with
                  | Some bs ->
                    do_if_verbose (fun _ ->
                    print_endline "cache hit");
                    bs
                  | None ->
                    do_if_verbose (fun _ ->
                    print_endline "cache miss");
                    let possible_branches =
                      List.concat_map
                        ~f:(fun (p,t) ->
                            let make_match pn e =
                              Option.map
                                ~f:(fun pn -> pnode_to_exp pn)
                                (integrate_path
                                   p
                                   pn
                                   e)
                            in
                            let lower_tests_outputs =
                              (List.map
                                 ~f:(fun (b,e1,e2,otm) ->
                                     (b,e1,e2,fun e ->
                                         InternalNode
                                           (List.map
                                              ~f:(fun pn ->
                                                  begin match make_match pn e with
                                                    | None -> NonexistantLeaf
                                                    | Some e -> otm e
                                                  end)
                                              pns)))
                                 relevant_tests_outputs)
                            in
                            let es =
                              propogate_exps
                                ~short_circuit:sc
                                true
                                ~search_matches:true
                                (*(fun e ->
                                   Output.create
                                     (List.concat_map
                                     ~f:(fun pn ->
                                         begin match make_match pn e with
                                           | None -> [None]
                                           | Some e -> (exp_to_output e).node
                                         end)
                                     pns))*)
                                lower_tests_outputs
                                (*(fun e ->
                                   snd @$
                                   Option.value_exn
                                     (List.max_elt
                                        ~compare:(pair_compare Float.compare (fun _ _ -> 0))
                                        (List.map
                                           ~f:(fun pn ->
                                               let ts = tests (make_match pn e) in
                                               (test_performance_to_ranking ts,ts))
                                           pns)))*)
                                t
                            in
                            let es =
                              minimize
                                size
                                es
                                lower_tests_outputs
                            in
                            List.map
                              ~f:(fun e -> (p,e))
                              es
                              (*let pppns =
                                cartesian_map
                                  ~f:(fun pn e -> (p,pn,e))
                                  pns
                                  es
                                in
                                let pppns =
                                select_any_improve
                                  pppns
                                  (List.map
                                     ~f:(fun (_,run) ->
                                         fun (p,e,pn) ->
                                           begin match (integrate_path p e pn) with
                                             | None -> false
                                             | Some e -> run (pnode_to_exp e)
                                           end)
                                     relevant_tests)
                                in
                                let pppns =
                                deduper
                                  (fun (p,pn,e) ->
                                     begin match integrate_path p pn e with
                                       | None -> List.map ~f:(fun _ -> None) (exp_to_output e)
                                       | Some pn -> exp_to_output (pnode_to_exp pn)
                                     end)
                                  (fun (p,pn,e) ->
                                     begin match integrate_path p pn e with
                                       | None -> Int.max_value
                                       | Some pn ->
                                         size (pnode_to_exp pn)
                                     end)
                                  pppns
                                in
                                ((p,t),pppns)*))
                        (*(fun (p,e,pn) ->
                                 List.map
                                   ~f:(fun (_,run) -> run (pnode_to_exp (integrate_path p e pn))))*)
                        (*Option.map
                          ~f:(fun (pn,f) -> (es,pn,f))
                          (select_tops
                             pns
                             (fun e ->
                                test_performance_to_ranking
                                  (List.map ~f:(fun (_,run) -> run (pnode_to_exp e)) tests))
                             (*(test_performance_to_ranking % tests % pnode_to_exp)*)
                             (size % pnode_to_exp)))*)
                        ppaths
                    in
                    update_solution_cache t pns_size prior_tests relevant_tests_outputs possible_branches;
                    possible_branches
                end
              in
              let pn_to_pnt (ts:exp tests_outputs) pn =
                (pn
                ,List.filter
                    ~f:(fun (b,_,_,otm) ->
                        b && not (passable_test_output_tree (otm (pnode_to_exp pn))))
                    ts)
              in
              (*List.iter
                ~f:(fun pn -> print_endline (Pp.pp_exp (pnode_to_exp pn)))
                pns;*)
              let pns =
                List.fold_until_completion
                  ~f:(fun (incompleted_pnts,completed_pns) ->
                      let (newly_completed_pnts,incompleted_pnts) =
                        List.partition_tf
                          ~f:(fun (_,ts) -> List.length ts = 0)
                          incompleted_pnts
                      in
                      let newly_completed_pns =
                        List.map
                          ~f:fst
                          newly_completed_pnts
                      in
                      let completed_pns = newly_completed_pns@completed_pns in
                      if List.length incompleted_pnts = 0 then
                        Right completed_pns
                      else
                        let incompleted_pnts =
                          List.cartesian_filter_map
                            ~f:(fun (p,e) (pn,ts) ->
                                Option.bind
                                  ~f:(fun pn ->
                                      let (pn,ts') = pn_to_pnt ts pn in
                                      if List.length ts = List.length ts' then
                                        None
                                      else
                                        Some (pn,ts'))
                                  (integrate_path p pn e))
                            possible_branches
                            incompleted_pnts
                        in
                        let incompleted_pnts =
                          deduper
                            (tests_outputs_update (pnode_to_exp % fst) all_tests_outputs)
                            (size % pnode_to_exp % fst)
                            incompleted_pnts
                        in
                        Left (incompleted_pnts,completed_pns)
                    )
                  (List.map ~f:(pn_to_pnt all_tests_outputs) pns,[])
              in
              let pns =
                deduper
                  (tests_outputs_update pnode_to_exp all_tests_outputs)
                  (size % pnode_to_exp)
                  pns
              in
              (*let (progressed_branches,remaining_branches) =
                split_by_condition
                  ~f:(fun (_,xs) -> not (List.is_empty xs))
                  integrations_rank_os
                in
                let progressed_branches_nodes =
                  List.map
                    ~f:snd
                    progressed_branches
                in
                let remaining_branches =
                  List.map
                    ~f:fst
                    remaining_branches
                in
                print_endline (string_of_int (List.length progressed_branches_nodes));
                (*let integrations_ranks_o = distribute_option integrations_rank_os in*)
                print_endline "NOOO";
                let all_combos = combinations progressed_branches_nodes in
                print_endline (List.to_string ~f:(fun (e,_) -> Pp.pp_exp e) relevant_tests);
                print_endline "ooon";
                let filtered_combos =
                  List.filter_map
                    ~f:(fun combo ->
                        begin match combo with
                          | (p,pn,e)::t ->
                            snd @$
                            List.fold_left
                              ~f:(fun (pn,pno) (p,pn',e) ->
                                  begin match pno with
                                    | None -> (pn,None)
                                    | Some pn'' ->
                                      if pn = pn' then
                                        (pn,integrate_path p pn'' e)
                                      else
                                        (pn,None)
                                  end)
                              ~init:(pn,integrate_path p pn e)
                              t
                          | _ -> failwith "pleaseno"
                        end)
                    all_combos
                in
                print_endline (string_of_int (List.length filtered_combos));
                print_endline "hi";
                let final_pns =
                  List.filter
                    ~f:(fun pn ->
                        List.for_all
                          ~f:(fun (_,run) -> run (pnode_to_exp pn))
                          relevant_tests)
                    filtered_combos
                in*)
              if List.is_empty pns then
                Right []
              else
                let prior_tests_outputs = prior_tests@relevant_tests_outputs in
                Left (pns,next_tests_outputs,prior_tests_outputs)
          in

          if not (List.is_empty passing) then
            Right passing
          else if not (any_nonforced_matches t) then
            standard_calc ()
          else
            begin
              let possible_branches =
                List.concat_map
                  ~f:(fun (p,t) ->
                      let make_match pn e =
                        Option.map
                          ~f:(fun pn -> pnode_to_exp pn)
                          (integrate_path
                             p
                             pn
                             e)
                      in
                      let lower_tests_outputs =
                        (List.map
                           ~f:(fun (b,e1,e2,otm) ->
                               (b,e1,e2,fun e ->
                                   InternalNode
                                     (List.map
                                        ~f:(fun pn ->
                                            begin match make_match pn e with
                                              | None -> NonexistantLeaf
                                              | Some e -> otm e
                                            end)
                                        pns)))
                           tests_outputs)
                      in
                      let es =
                        propogate_exps
                          ~short_circuit:sc
                          true
                          ~search_matches:false
                          (*(fun e ->
                             Output.create
                               (List.concat_map
                               ~f:(fun pn ->
                                   begin match make_match pn e with
                                     | None -> [None]
                                     | Some e -> (exp_to_output e).node
                                   end)
                               pns))*)
                          lower_tests_outputs
                          (*(fun e ->
                             snd @$
                             Option.value_exn
                               (List.max_elt
                                  ~compare:(pair_compare Float.compare (fun _ _ -> 0))
                                  (List.map
                                     ~f:(fun pn ->
                                         let ts = tests (make_match pn e) in
                                         (test_performance_to_ranking ts,ts))
                                     pns)))*)
                          t
                      in
                      let es =
                        minimize
                          size
                          es
                          lower_tests_outputs
                      in
                      List.map
                        ~f:(fun e -> (p,e))
                        es
                        (*let pppns =
                          cartesian_map
                            ~f:(fun pn e -> (p,pn,e))
                            pns
                            es
                          in
                          let pppns =
                          select_any_improve
                            pppns
                            (List.map
                               ~f:(fun (_,run) ->
                                   fun (p,e,pn) ->
                                     begin match (integrate_path p e pn) with
                                       | None -> false
                                       | Some e -> run (pnode_to_exp e)
                                     end)
                               relevant_tests)
                          in
                          let pppns =
                          deduper
                            (fun (p,pn,e) ->
                               begin match integrate_path p pn e with
                                 | None -> List.map ~f:(fun _ -> None) (exp_to_output e)
                                 | Some pn -> exp_to_output (pnode_to_exp pn)
                               end)
                            (fun (p,pn,e) ->
                               begin match integrate_path p pn e with
                                 | None -> Int.max_value
                                 | Some pn ->
                                   size (pnode_to_exp pn)
                               end)
                            pppns
                          in
                          ((p,t),pppns)*))
                  (*(fun (p,e,pn) ->
                           List.map
                             ~f:(fun (_,run) -> run (pnode_to_exp (integrate_path p e pn))))*)
                  (*Option.map
                    ~f:(fun (pn,f) -> (es,pn,f))
                    (select_tops
                       pns
                       (fun e ->
                          test_performance_to_ranking
                            (List.map ~f:(fun (_,run) -> run (pnode_to_exp e)) tests))
                       (*(test_performance_to_ranking % tests % pnode_to_exp)*)
                       (size % pnode_to_exp)))*)
                  ppaths
              in
              let pn_to_pnt (ts:exp tests_outputs) pn =
                (pn
                ,List.filter
                    ~f:(fun (b,_,_,otm) ->
                        b && not (passable_test_output_tree (otm (pnode_to_exp pn))))
                    ts)
              in
              let pns =
                List.fold_until_completion
                  ~f:(fun (incompleted_pnts,completed_pns) ->
                      let (newly_completed_pnts,incompleted_pnts) =
                        List.partition_tf
                          ~f:(fun (_,ts) -> List.length ts = 0)
                          incompleted_pnts
                      in
                      let newly_completed_pns =
                        List.map
                          ~f:fst
                          newly_completed_pnts
                      in
                      let completed_pns = newly_completed_pns@completed_pns in
                      if List.length completed_pns > 0 || List.length incompleted_pnts = 0 then
                        Right completed_pns
                      else
                        let incompleted_pnts =
                          List.cartesian_filter_map
                            ~f:(fun (p,e) (pn,ts) ->
                                Option.bind
                                  ~f:(fun pn ->
                                      let (pn,ts') = pn_to_pnt ts pn in
                                      if List.length ts = List.length ts' then
                                        None
                                      else
                                        Some (pn,ts'))
                                  (integrate_path p pn e))
                            possible_branches
                            incompleted_pnts
                        in
                        let incompleted_pnts =
                          deduper
                            (tests_outputs_update (pnode_to_exp % fst) tests_outputs)
                            (size % pnode_to_exp % fst)
                            incompleted_pnts
                        in
                        Left (incompleted_pnts,completed_pns)
                    )
                  (List.map ~f:(pn_to_pnt tests_outputs) pns,[])
              in
              let pns =
                deduper
                  (tests_outputs_update pnode_to_exp tests_outputs)
                  (size % pnode_to_exp)
                  pns
              in
              (*let (progressed_branches,remaining_branches) =
                split_by_condition
                  ~f:(fun (_,xs) -> not (List.is_empty xs))
                  integrations_rank_os
                in
                let progressed_branches_nodes =
                  List.map
                    ~f:snd
                    progressed_branches
                in
                let remaining_branches =
                  List.map
                    ~f:fst
                    remaining_branches
                in
                print_endline (string_of_int (List.length progressed_branches_nodes));
                (*let integrations_ranks_o = distribute_option integrations_rank_os in*)
                print_endline "NOOO";
                let all_combos = combinations progressed_branches_nodes in
                print_endline (List.to_string ~f:(fun (e,_) -> Pp.pp_exp e) relevant_tests);
                print_endline "ooon";
                let filtered_combos =
                  List.filter_map
                    ~f:(fun combo ->
                        begin match combo with
                          | (p,pn,e)::t ->
                            snd @$
                            List.fold_left
                              ~f:(fun (pn,pno) (p,pn',e) ->
                                  begin match pno with
                                    | None -> (pn,None)
                                    | Some pn'' ->
                                      if pn = pn' then
                                        (pn,integrate_path p pn'' e)
                                      else
                                        (pn,None)
                                  end)
                              ~init:(pn,integrate_path p pn e)
                              t
                          | _ -> failwith "pleaseno"
                        end)
                    all_combos
                in
                print_endline (string_of_int (List.length filtered_combos));
                print_endline "hi";
                let final_pns =
                  List.filter
                    ~f:(fun pn ->
                        List.for_all
                          ~f:(fun (_,run) -> run (pnode_to_exp pn))
                          relevant_tests)
                    filtered_combos
                in*)
              if not (List.is_empty pns) then
                Right pns
              else
                standard_calc ()
                (*begin match integrations_ranks_o with
                  | None -> Right []
                  | Some integrations_ranks ->
                    let maxes_indices =
                      retrieve_maxes_and_indices
                        integrations_ranks
                        (fun (_,_,f1) (_,_,f2) -> Float.compare f1 f2)
                    in
                    if List.length maxes_indices = 0 then
                      failwith "cannot happen no"
                    else if List.length maxes_indices = 1 then
                      let ((_,pns,f),i) = List.hd_exn maxes_indices in
                      print_endline (Float.to_string f);
                      let pns =
                        deduper
                          (exp_to_output % pnode_to_exp)
                          (size % pnode_to_exp)
                          pns
                      in
                      List.iter
                        ~f:(fun pn -> print_endline (Pp.pp_exp (pnode_to_exp pn)))
                        pns;
                      List.iter
                        ~f:(fun pn -> print_endline (List.to_string ~f:(string_of_pair Pp.pp_exp Bool.to_string) (List.map ~f:(fun (v,run) -> (v,run (pnode_to_exp pn))) tests)))
                        pns;
                      print_endline (string_of_int (List.length pns));
                      let (_,bs) = remove_at_index_exn bs i in
                      let tests =
                        List.filter
                          ~f:(fun (_,run) ->
                              List.exists
                                ~f:(fun pn -> not (run (pnode_to_exp pn)))
                                pns)
                          tests
                      in
                      List.iter
                        ~f:(fun pn -> print_endline (List.to_string ~f:(string_of_pair Pp.pp_exp Bool.to_string) (List.map ~f:(fun (v,run) -> (v,run (pnode_to_exp pn))) tests)))
                        pns;
                      print_endline "next";
                      Left (pns,bs,tests)
                    else
                      failwith "TODO"
                  end*)
            end)
    ([Node (retrieve_match_exp_exn t,[])],tests_outputs,[])
  in
  let ppeos =
    List.map
      ~f:(fun (pp,rt) ->
          let es =
            propogate_exps
              ~short_circuit:false
              true
              []
              rt
              ~search_matches:false
          in
          let es_sized =
            List.map
              ~f:(fun e -> (e,size e))
              es
          in
          let sorted_sized_es =
            List.sort
              ~compare:(fun (_,s1) (_,s2) -> Int.compare s1 s2)
              es_sized
          in
          begin match sorted_sized_es with
            | [] -> None
            | _ ->
              let sorted_sized_es =
                List.take
                  sorted_sized_es
                  (Float.to_int (10000. ** (1. /. (Float.of_int (List.length ppaths)))))
              in
              let es =
                List.map
                  ~f:fst
                  sorted_sized_es
              in
              Some (pp,es)
          end)
      ppaths
  in
  let ppes_o = Some (List.filter_map ppeos ~f:Fn.id) in
  begin match ppes_o with
    | None -> []
    | Some ppes ->
  (List.concat_map
     ~f:(fun pn ->
         List.map
           ~f:pnode_to_exp
           (List.fold_left
              ~f:(fun pns (pp,es) ->
                  let ans =
                    List.cartesian_filter_map
                      ~f:(integrate_path pp)
                      pns
                      es
                  in
                  if ans = [] then
                    pns
                  else
                    ans)
              ~init:[pn]
              ppes))
     pns)
  end

(***** }}} *****)

(***** }}} *****)

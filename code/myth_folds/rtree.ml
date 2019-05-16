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
  : rtree =
  begin match Gamma.peel_nonrecursive_variant g s with
    | None ->
      { t         = t
      ; sz        = 1
      ; g         = g
      ; es        = []
      ; timed_out = false
      ; matches   = if matches_count <= 0 then None
          else Some (create_matches s g env t matches_count 1 !scrutinee_size_lim)
      ; refinements  = create_non_matches s g env t matches_count
      ; scrutinee_size = !scrutinee_size_lim
      ; forced_match = false
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
      (p, create_rtree s g env t (matches-1))) branches
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
    [SAbs (f, (x, t1), t2, create_rtree s g env t2 matches)]

  (* Refine tuples *)
  | TTuple ts ->
      let trees =
        List.map ~f:(fun t -> create_rtree s g env t matches) ts
      in
      [STuple trees]

  (* Refine records *)
  | TRcd _ -> []

(***** }}} *****)

(* Grows the given refinement tree by one level of matches. *)
let rec grow_matches (s:Sigma.t) (env:env) (t:rtree) =
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
  : 'a list * Float.t =
  let e_rank = List.map ~f:(fun e -> (e,ranking e)) es in
  let sorted_e_rank = List.sort ~compare:(fun (_,f1) (_,f2) -> Float.compare f2 f1) e_rank in
  begin match sorted_e_rank with
    | [] -> failwith "shouldnt happen i hope"
    | (e,r)::t ->
      if r = 1. then
        ([e],1.)
      else
        (e::
        (List.map
           ~f:fst
           (List.take_while ~f:(fun (_,r') -> r = r') t)),r)
  end

let retrieve_max_and_index
    (l:'a list)
    (cmp:'a -> 'a -> int)
  : 'a * int =
  let open MyStdlib in
  begin match l with
    | [] -> failwith "cannot"
    | h::t ->
      List.foldi
        ~f:(fun i (accv,acci) x ->
            if cmp accv x < 0 then
              (x,i+1)
            else
              (accv,acci))
        ~init:(h,0)
        t
  end

type pnode =
  | Node of exp * (pat * pnode) list
  | Leaf of exp

type ppath = (exp * pat) list

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
    (exp_finder:rtree -> exp list)
  : (ppath * exp list) list =
  if t.forced_match then
    let (e,prts) = List.hd_exn (Option.value_exn t.matches) in
    List.concat_map
      ~f:(fun (p,rt) ->
          let ppess = retrieve_force_match_ppaths rt exp_finder in
          List.map ~f:(fun (pp,es) -> ((e,p)::pp,es)) ppess)
      prts
  else
    [[],exp_finder t]

let rec integrate_path
    (pp:ppath)
    (pn:pnode)
    (e_base:exp)
  : pnode =
  begin match (pn,pp) with
    | (Node (e,ppns), (_,p)::t) ->
      let p_update =
        fun (p',pn') ->
          if p = p' then
            Some (p',integrate_path t pn' e_base)
          else
            None
      in
      begin match update_first ~f:p_update ppns with
        | None -> Node (e,(p,ppath_to_pnode t e_base)::ppns)
        | Some ppns -> Node (e,ppns)
      end
    | _ -> failwith "shouldn't happen"
  end

let rec propogate_exps ?short_circuit:(sc = true) (condition:exp -> Float.t) (t:rtree) : exp list =
  if sc && List.length t.es > 0 then
    t.es
  else
    (* NOTE: Prioritize lambdas, matches, and then constructors, in that order. *)
    let es = t.es
             @ propogate_exps_matches ~short_circuit:sc condition t
             @ List.concat_map ~f:(propogate_exps_node ~short_circuit:sc condition) t.refinements
    in
    t.es <- es;
    es

and propogate_exps_matches ?short_circuit:(sc = true) (condition:exp -> Float.t) (t:rtree) : exp list =
  if t.forced_match then
    propagate_enforced_matches ~short_circuit:sc condition t
  else
    match t.matches with
    | None -> []
    | Some ms -> List.concat_map ~f:(propogate_exps_rmatch ~short_circuit:sc condition) ms

and propogate_exps_rmatch ?short_circuit:(sc = true) (condition:exp -> Float.t) (m:rmatch) : exp list =
  let (e, bs)  = m in
  (*let (ps, ts) = List.unzip bs in*)
  let branches =
    List.fold_left
      ~f:(fun bss (p,t) ->
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
          let t_es = propogate_exps ~short_circuit:sc new_condition t in
          let pe = List.map ~f:(fun e -> (p,e)) t_es in
          let non_projected = Util.cartesian_map ~f:List.cons pe bss in
          let ans = select_tops
              non_projected
              (fun bs -> condition (EMatch (e,bs))) in
           fst ans)
      ~init:([[]])
      bs
  in
  List.map ~f:(fun bs -> EMatch (e, bs)) branches

and propogate_exps_node ?short_circuit:(sc = true) (condition:exp -> Float.t) (n:rnode) : exp list =
  match n with
  | SUnit -> [EUnit]

  | SAbs (f, x, ty, t) ->
    let e_transformer = fun e -> EFix (f, x, ty, e) in
    List.map ~f:e_transformer (propogate_exps ~short_circuit:sc (fun e -> (condition (e_transformer e)) ) t)

  | SCtor (c, t) ->
      propogate_exps ~short_circuit:sc condition t |> List.map ~f:(fun e -> ECtor (c, e))

  | STuple ts ->
      List.map ~f:(propogate_exps ~short_circuit:sc condition) ts
        |> Util.combinations
        |> List.map ~f:(fun es -> ETuple es)

  | SRcd ts ->
      List.map ~f:(fun (l,t) ->
        List.map ~f:(fun e -> (l,e)) (propogate_exps ~short_circuit:sc condition t)) ts
        |> Util.combinations
        |> List.map ~f:(fun es -> ERcd es)

and propagate_enforced_matches
    ?short_circuit:(sc = true)
    (condition:exp -> Float.t)
    (t:rtree)
  : exp list =
  let open MyStdlib in
  let ppaths = retrieve_force_match_ppaths t (propogate_exps ~short_circuit:sc condition) in
  fold_until_completion
    ~f:(fun (pns,bs) ->
        if bs = [] then
          Right (List.map ~f:pnode_to_exp pns)
        else
          let integrations_ranks =
            List.map
              ~f:(fun (p,es) ->
                  print_endline ("PNS SIZE " ^ (string_of_int (List.length pns * List.length es)));
                  let pns =
                    cartesian_map
                      ~f:(integrate_path p)
                      pns
                      es
                  in
                  select_tops
                    pns
                    (condition % pnode_to_exp))
              bs
          in
          let ((pns,f),i) =
            retrieve_max_and_index
              integrations_ranks
              (fun (_,f1) (_,f2) -> Float.compare f1 f2)
          in
          print_endline ("chose " ^ (string_of_int i));
            print_endline (Float.to_string f);
          let (_,bs) = remove_at_index_exn bs i in
          Left (pns,bs))
    ([Node (retrieve_match_exp_exn t,[])], ppaths)

(***** }}} *****)

(***** }}} *****)

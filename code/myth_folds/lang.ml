open Core
open Printf

(**** Language {{{ *****)

type id = string
[@@deriving ord, show, hash]

type label = string
[@@deriving ord, show, hash]

type 'a record = (label * 'a) list
[@@deriving ord, show, hash]

type typ =
  | TBase of id
  | TArr  of typ * typ
  | TTuple of typ list (* Invariant: List must always have two members. *)
  | TRcd of typ record
  | TUnit
[@@deriving ord, show, hash]

let get_base_exn (t:typ)
  : string =
  begin match t with
    | TBase i -> i
    | _ -> failwith "bad base"
  end

type ctor = id * typ
[@@deriving ord, show, hash]

module Ctor = struct
  type t = ctor
  [@@deriving ord, show, hash]
end

type pattern =
  | PWildcard
  | PVar of id
  | PTuple of pattern list
  | PRcd of pattern record

type pat = id * (pattern option)   (* (id of constructor, pattern). *)

type arg = id * typ

type env = (id * value) list

and decl =
  | DData of id * ctor list
  | DLet  of id * bool * arg list * typ * exp

and exp =
  | EVar of id
  | EApp of exp * exp
  | EFun of arg * exp
  | ELet of id * bool * arg list * typ * exp * exp
  | ECtor of id * exp
  | EMatch of exp * branch list
  | EPFun of (exp * exp) list
  | EFix of id * arg * typ * exp
  | ETuple of exp list  (* Invariant: List must always have two members. *)
  | EProj of int * exp  (* int is the index of projection of the tuple (1-indexed). *)
  | ERcd of exp record
  | ERcdProj of (label * exp)
  | EUnit

and branch = pat * exp

and value =
  | VCtor  of id * value
  | VFun   of id * exp * env ref
  | VPFun  of (value * value) list
  | VTuple of value list (* Invariant: List must always have two members. *)
  | VRcd of value record
  | VUnit

module Type = struct
  type t = typ
  [@@deriving ord, show, hash]
end

let compare_val (v1:value) (v2:value) : int =
  compare v1 v2

let compare_exp (e1:exp) (e2:exp) : int =
  compare e1 e2

let compare_decl (d1:decl) (d2:decl) : int =
  compare d1 d2

type synth_problem = id * typ * exp list

type prog = decl list * synth_problem

exception Internal_error of string
let internal_error f s = raise @@ Internal_error (sprintf "(%s) %s" f s)

let rec hash_typ = function
  | TUnit   -> 1
  | TBase x -> String.hash x
  | TArr (t1, t2) -> abs ((hash_typ t1) + 79 * (hash_typ t2) + 73)
  | TTuple ts -> List.fold_left
      ~f:(fun acc ty -> acc + 79 * (hash_typ ty) + 73)
      ~init:73
      ts
  | TRcd ts -> List.fold_left
      ~f:(fun acc (lbl,ty) ->
            acc + 79 * (String.hash lbl) + 79 * (hash_typ ty) + 73 )
      ~init:73
      ts

let rec types_to_arr (ts:typ list) =
  match ts with
  | []  -> internal_error "types_to_arr" "empty type list provided"
  | [t] -> t
  | t :: ts -> TArr (t, types_to_arr ts)

let rec free_vars (e:exp) : id list =
  match e with
  | EVar x -> [x]
  | EApp (e1, e2) -> free_vars e1 @ free_vars e2
  | EFun (_, e) -> free_vars e
  | ELet (_, _, _, _, e1, e2) -> free_vars e1 @ free_vars e2
  | ECtor (_, e) -> free_vars e
  | ETuple es -> List.map ~f:free_vars es |> List.concat
  | EProj (_, e) -> free_vars e
  | ERcd es -> List.map ~f:(fun (_,e) -> free_vars e) es |> List.concat
  | ERcdProj (_, e) -> free_vars e
  | EMatch (e, bs) ->
    List.map ~f:(fun (_, e) -> free_vars e) bs
      |> List.concat
      |> (@) (free_vars e)
  | EPFun ios ->
    List.fold_left
      ~f:(fun acc (e1, e2) -> acc @ free_vars e1 @ free_vars e2)
      ~init:[] ios
  | EFix (_, _, _, e) -> free_vars e
  | EUnit -> []

let rec size (e:exp) : int =
  match e with
  | EVar _ -> 1
  | EApp (e1, e2) -> 1 + size e1 + size e2
  | EFun (_, e) -> 1 + size e
  | ELet (_, _, _, _, e1, e2) -> 1 + size e1 + size e2
  | ECtor (_, e) -> 1 + size e
  | ETuple es -> 1 + List.fold_left ~f:(fun n e -> n + size e) ~init:0 es
  | EProj (_, e) -> 1 + size e
  | ERcd es -> 1 + List.fold_left ~f:(fun n (_,e) -> n + size e) ~init:0 es
  | ERcdProj (_, e) -> 1 + size e
  | EMatch (e, bs) ->
      1 + size e + List.fold_left ~f:(fun n (_, e) -> n + size e) ~init:0 bs
  | EPFun ios -> 1 +
      List.fold_left ~f:(fun n (e1, e2) -> n + size e1 + size e2) ~init:0 ios
  | EFix (_, _, _, e) -> 1 + size e
  | EUnit -> 1

let rec examples_count (v:value) : int =
  match v with
  | VPFun ios ->
      List.fold_left ~f:(fun n (_, v) -> n + examples_count v) ~init:0 ios
  | _ -> 1

let rec extract_ids_from_pattern = function
  | PWildcard -> []
  | PVar x    -> [x]
  | PTuple ps -> List.concat_map ~f:extract_ids_from_pattern ps
  | PRcd ps   -> List.concat_map ~f:(fun (_,p) -> extract_ids_from_pattern p) ps

let gen_var_base (t:typ) : id =
  match t with
  | TArr (_, _) -> "f"
  | TBase dt    -> dt.[0] |> Char.lowercase |> String.make 1
  | TTuple _    -> "t"
  | TRcd _      -> "r"
  | TUnit       -> "u"

let rec contains
    (e1:exp)
    (e2:exp)
  : bool =
  let contains_rec = fun e -> contains e e2 in
  if e1 = e2 then
    true
  else
    begin match e1 with
      | EApp (e1,e2) -> contains_rec e1 || contains_rec e2
      | EFun (_,e) -> contains_rec e
      | ELet (_,_,_,_,e1,e2) -> contains_rec e1 || contains_rec e2
      | ECtor (_,e) -> contains_rec e
      | EMatch (e,bs) ->
        contains_rec e ||
        List.exists
          ~f:(fun (_,e) -> contains_rec e)
          bs
      | EPFun eps ->
        List.exists
          ~f:(fun (e1,e2) -> contains_rec e1 || contains_rec e2)
          eps
      | EFix (_,_,_,e) -> contains_rec e
      | ETuple es ->
        List.exists
          ~f:contains_rec
          es
      | EProj (_,e) -> contains_rec e
      | ERcd rs ->
        List.exists
          ~f:(fun (_,e) -> contains_rec e)
          rs
      | ERcdProj (_,e) -> contains_rec e
      | EUnit
      | EVar _ -> false
    end

(***** }}} *****)

open Core
open Lang
open Datastructures
open Util.Operators
open Sigma

(***** The main Gamma module {{{ *****)

module type Gamma_Sig = sig
    type t

    val empty : t

    (* Insert ids, which are automatically focused.                                       *)
    val insert                   : id -> typ -> bool -> t -> t
    val insert_pattern           : typ -> t -> (pattern * t)
    val mark_as_rec_fun_with_arg : id -> id -> t -> t
    val mark_as_arg_of_fun       : id -> id -> t -> t
    val mark_as_dec_arg_of_fun   : id -> id -> t -> t

    (* Insert an expression, which is not focused.                                        *)
    val insert_exp      : exp -> typ -> t -> t

    (* Look up ids.                                                                       *)
    val peel            : t -> ((exp * typ) * t) option
    val lookup_type     : id -> t -> typ option
    val lookup_type_exn : id -> t -> typ

    (*val deactivate      : t -> id -> t*)
    val contains_variant : exp -> t -> bool
    val remove_variant : t -> exp -> t
    val peel_nonrecursive_variant : t -> Sigma.t -> ((exp * typ) * t) option

    (* Check properties of ids.                                                           *)
    val is_rec_fun      : exp -> t -> bool
    val fun_of_arg      : exp -> t -> id option (* Only works for recursive functions. *)
    val is_valid_app    : exp -> exp -> t -> bool

    (* Retrieve active expressions.                                                       *)
    val active          : t -> (exp * typ) list
    val active_of_type  : typ -> t -> exp list
    val last_added      : t -> exp option
    val types           : t -> typ list

    (* Other useful functions.                                                            *)
    val fresh_id        : id -> t -> id
    val hash            : t -> int
    val pp              : t -> string
end

module Gamma_Struct (Dict : Dictionary) : Gamma_Sig = struct
    module Set = SetOfDictionary(Dict)

    type t = { active     : (exp,  typ) Dict.t
             ; recent     : (exp * typ) list
             ; ids        : (id,   typ) Dict.t
             ; variant    : exp Set.t
             ; fun_to_arg : (id, id  Set.t) Dict.t  (* recursive funcs to their args.   *)
             ; arg_to_fun : (id, id * bool) Dict.t  (* true if it is a decreasing arg.  *)
    }

    (* Prints a context.                                                                *)
    let pp (g:t) =
        let pp_args x = match Dict.find x g.fun_to_arg with
          | Some s -> 
              if Set.is_empty s then ""
              else "[args: " ^ (String.concat ~sep:" " (Set.keys s)) ^ "]"
          | None -> ""
        in
        let pp_arg_of x = match Dict.find x g.arg_to_fun with
          | Some (f, dec) -> if dec then "[dec arg of " ^ f ^ "]" else "[arg of " ^ f ^ "]"
          | None          -> ""
        in
        let pp_id x =
          let t = Dict.find_exn x g.ids in
          Printf.sprintf "%s : %s %s %s" x (Pp.pp_typ t) (pp_args x) (pp_arg_of x)
        in
        let ids_str = String.concat ~sep:"\n" (List.map ~f:pp_id (Dict.keys g.ids)) in

        let pp_exp e =
          let t = Dict.find_exn e g.active in
          Printf.sprintf "%s : %s" (Pp.pp_exp e) (Pp.pp_typ t)
        in
        let active_str =
          String.concat ~sep:"\n" (List.map ~f:pp_exp (Dict.keys g.active))
        in

        let pp_recent (e, t) = 
          Printf.sprintf "%s : %s" (Pp.pp_exp e) (Pp.pp_typ t)
        in
        let recent_str = String.concat ~sep:"\n" (List.map ~f:pp_recent g.recent) in

        "--------------------\nids:\n--------------------\n" ^ ids_str ^
        "\n--------------------\nactive:\n--------------------\n" ^ active_str ^
        "\n--------------------\nrecent:\n--------------------\n" ^ recent_str ^ "\n"

    (* Returns a fresh name that is not currently in use.                                 *)
    let fresh_id (base:id) (g:t) : id =
      let rec fresh n =
        let x = sprintf "%s%d" base n in
        match Dict.find x g.ids with
        | Some _ -> fresh (n+1)
        | _ -> x
      in
      fresh 1

    (* Only projection and variables are valid inhabitants of contexts.                   *)
    let rec cmp_exp e1 e2 = match (e1, e2) with
      | (EVar s1, EVar s2) -> s1 = s2
      | (EProj (n1, e1'), EProj (n2, e2')) -> n1 = n2 && cmp_exp e1' e2'
      | (ERcdProj (l1, e1'), ERcdProj (l2, e2')) -> l1 = l2 && cmp_exp e1' e2'
      | _ -> false

    let empty = {
        active     = Dict.empty cmp_exp;
        ids        = Dict.empty (=);
        variant    = Set.empty  cmp_exp;
        recent     = [];
        fun_to_arg = Dict.empty (=);
        arg_to_fun = Dict.empty (=);
    }

    (* Generate a pattern for a type that is inserted.  Essentially explicit focusing.    *)
    let rec insert_pattern (t:typ) (g:t) : pattern * t = match t with
      | TUnit -> (PWildcard, g)

      | TBase _ | TArr _ ->
        let x = fresh_id (gen_var_base t) g in
        (PVar x, 
        { g with active = Dict.set (EVar x) t g.active
               ; ids = Dict.set x t g.ids
               ; recent = (EVar x, t) :: g.recent
               ; variant = Set.add (EVar x) g.variant
        })

      | TTuple ts ->
        let (ps, g) = List.fold_right
          ~f:(fun t (ps, g) -> let (p, g') = insert_pattern t g in (p::ps, g'))
          ~init:([], g)
          (List.rev ts) (* Ensures variable numbering increases (t1, t2, ...).            *)
        in
        (PTuple (List.rev ps), g)

      | TRcd ts ->
          let (ps, g) = List.fold_left ts ~init:([], g)
            ~f:(fun (ps, g) (l,t) ->
              let (p, g') = insert_pattern t g
              in ((l,p)::ps, g'))
          in (PRcd ps, g)

    (* Focus an expression down to its constituents.                                      *)
    let rec focus (e:exp) (t:typ) : (exp * typ) list =
      begin match t with
      | TUnit | TArr _ | TBase _ -> [(e, t)]
      | TTuple ts -> List.concat_mapi ~f:(fun i t -> focus (EProj (i+1, e)) t) ts
      | TRcd ts -> List.concat_map ~f:(fun (l,t) -> focus (ERcdProj (l, e)) t) ts
      end

    (* Insert ids, which are automatically focused.                                       *)
    let insert (x:id) (t:typ) (is_variant:bool) (g:t) =
      let focused = focus (EVar x) t in
      let active' = List.fold_left ~f:(fun a (e, t) -> Dict.set e t a)
                                   ~init:g.active
                                   focused
      in
      (* Remove all repeat entries from the recent list.                                  *)
      let recent' = List.filter ~f:(fun (e1, _) ->
         not (List.fold_left ~f:(fun acc (e2, _) -> acc || cmp_exp e1 e2) ~init:false focused))
         g.recent
      in
      let variant =
        if is_variant then
          List.fold_left
            ~f:(fun a (e,_) -> Set.add e a)
            ~init:g.variant
            focused
        else
          g.variant
      in
      { g with active = active'
             ; ids = Dict.set x t g.ids
             ; recent = focused @ recent'
             ; variant = variant
      }

    let remove_variant
        (g:t)
        (e:exp)
      : t =
      { g with
        variant = Set.remove e g.variant
      }


    (* Insert an expression, which is not focused.                                        *)
    let insert_exp (e:exp) (t:typ) (g:t) =
      { g with active = Dict.set e t g.active
      ; recent = (e, t) :: (List.filter ~f:(fun (e',_) -> not (cmp_exp e e')) g.recent)
      }

    (*let deactivate (g:t) (_:id) =
      print_endline (pp g);
      {
        g with active = Dict.remove (EVar "convert") g.active
      }*)

    let peel (g:t) : ((exp * typ) * t) option =
      match g.recent with
      | [] -> None
      | (e, t) :: tl ->
        Some ((e, t), { g with active = Dict.remove e g.active; recent = tl })

    (* PUBLIC: Mark the relationships between ids.                                        *)
    let mark_as_rec_fun_with_arg (f:id) (x:id) (g:t) =
      let s = match Dict.find f g.fun_to_arg with
              | Some s -> s
              | None -> Set.empty (=)
      in
      { g with fun_to_arg = Dict.set f (Set.add x s) g.fun_to_arg }

    let mark_as_arg_of_fun (x:id) (f:id) (g:t) =
      match Dict.find x g.arg_to_fun with
      | None -> { g with arg_to_fun = Dict.set x (f, false) g.arg_to_fun }
      | Some (f', _) ->
        if f = f' then g
        else failwith (Printf.sprintf "%s is arg of %s and can't be marked for %s" x f' f)

    let mark_as_dec_arg_of_fun (x:id) (f:id) (g:t) =
      match Dict.find x g.arg_to_fun with
      | None -> { g with arg_to_fun = Dict.set x (f, true) g.arg_to_fun }
      | Some (f', _) ->
        if f = f' then { g with arg_to_fun = Dict.set x (f, true) g.arg_to_fun }
        else failwith (Printf.sprintf "%s is arg of %s and can't be marked for %s" x f' f)

    (* Perform lookups.                                                                   *)
    let lookup_type     (x:id) (g:t) : typ option = Dict.find     x g.ids
    let lookup_type_exn (x:id) (g:t) : typ        = Dict.find_exn x g.ids

    let rec contains_variant (x:exp) (g:t) : bool =
      let contains_variant x = contains_variant x g in
      Set.has x g.variant ||
      begin match x with
        | EApp (e1,e2) -> contains_variant e1 || contains_variant e2
        | EFun (_,e) -> contains_variant e
        | ELet (_,_,_,_,e1,e2) -> contains_variant e1 || contains_variant e2
        | ECtor (_,e) -> contains_variant e
        | EMatch (e,branches) ->
          contains_variant e ||
          List.exists ~f:(fun (_,e) -> contains_variant e) branches
        | EPFun _ -> failwith "shouldnt"
        | EFix (_,_,_,e) -> contains_variant e
        | ETuple es -> List.exists ~f:contains_variant es
        | EProj (_,e) -> contains_variant e
        | ERcd _ -> failwith "shouldnt"
        | ERcdProj _ -> failwith "shouldnt"
        | EVar _
        | EUnit -> false
      end

    let rec peel_nonrecursive_variant
        (g:t)
        (s:Sigma.t)
      : ((exp * typ) * t) option =
      begin match g.recent with
        | [] -> None
        | (e, t) :: tl ->
          let calc_recursion () =
            Option.map
              ~f:(fun (et,g) ->
                  (et,
                   { g with
                     recent = (e,t)::g.recent
                   }))
              (peel_nonrecursive_variant
                 { g with
                   recent = tl
                 }
                 s)
          in
          begin match t with
            | TBase i ->
              if (Set.has e g.variant) && not (Sigma.is_recursive s i) then
                (Some
                   ((e,t),
                    { g with
                      recent = tl ;
                      variant = Set.remove e g.variant }))
              else
                calc_recursion ()
            | _ -> calc_recursion ()
          end
      end


    (* PRIVATE: Is f a recursive function?                                                *)
    let is_id_rec_fun (f:id) (g:t) : bool = Option.is_some (Dict.find f g.fun_to_arg)
      
    (* PRIVATE: Extract a recursive function id from e.                                   *)
    let extract_rec_fun_from_exp (e:exp) (g:t) : id option = match e with
      | EVar f -> if is_id_rec_fun f g then Some f else None
      | _ -> None 

    (* PUBLIC: Does e represent a recursive function?                                     *)
    let is_rec_fun (e:exp) (g:t) : bool =
      Option.is_some (extract_rec_fun_from_exp e g)

    (* PRIVATE: Is x a decreasing argument of f?                                          *)
    let is_id_dec_arg (x:id) (f:id) (g:t) : bool =
      match Dict.find x g.arg_to_fun with
      | Some (f', b) -> f = f' && b
      | None -> false

    (* PRIVATE: Extract an argument id from e.                                            *)
    let rec extract_arg_from_exp (e:exp) (g:t) : id option =
      match e with
      | EVar x -> Some x
      | EProj (_, e) -> extract_arg_from_exp e g
      | ERcdProj (_, e) -> extract_arg_from_exp e g
      | _ -> None

    (* PUBLIC: What function is e an argument of?                                        *)
    let fun_of_arg (e:exp) (g:t) : id option =
      extract_arg_from_exp e g            >?>
      (fun x -> Dict.find x g.arg_to_fun) >?>
      (fun (f, _) -> Some f)

    (* PUBLIC: Is an application valid?                                                  *)
    let is_valid_app (func:exp) (arg:exp) (g:t) =
      let rec is_dec_arg_of_func (arg:exp) (f:id) = match arg with
        | EVar x -> is_id_dec_arg x f g
        | EProj (_, e) -> is_dec_arg_of_func e f
        | ERcdProj (_, e) -> is_dec_arg_of_func e f
        | _ -> false
      in
      match extract_rec_fun_from_exp func g with
        | None -> true
        | Some f -> is_dec_arg_of_func arg f

    (* Retrieve active expressions.                                                       *)
    let active (g:t) = List.zip_exn (Dict.keys g.active) (Dict.vals g.active)

    let active_of_type (t:typ) (g:t) =
        let dict_of_type = Dict.filter (fun _ v -> v = t) g.active in
        Dict.keys dict_of_type

    let last_added (g:t) = match g.recent with
      | [] -> None
      | (e, _) :: _ -> Some e

    let types (g:t) = Util.nub (Dict.vals g.active)

    (* Hashes a context.                                                                 *)
    let hash (g:t) =
      let rec hash_exp = function
        | EVar x -> String.hash x
        | EProj (n, e) -> (Int.hash n) lxor (hash_exp e)
        | ERcdProj (n, e) -> (String.hash n) lxor (hash_exp e)
        | _ -> failwith "Cannot hash non-projections."
      in
      List.foldi
        ~f:(fun i ans (e, t) ->
            (hash_typ t) lxor (hash_exp e) lxor (Int.hash i) lxor ans)
        ~init:102397
        g.recent
end

module Gamma = Gamma_Struct(ListDictionary)

(***** }}} *****)

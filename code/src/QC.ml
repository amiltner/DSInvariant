open MyStdlib

type 'a g = int -> 'a option

let rec choice
    (gs:'a g list)
  : 'a g =
  let len = List.length gs in
  if len = 0 then
    (fun _ -> None)
  else
    let i = Random.int len in
    let base_g = List.nth_exn gs i in
    let g
        (s:int)
      : 'a option =
      let a_o = base_g s in
      if Option.is_some a_o then
        a_o
      else
        let gs = remove_at_exn gs i in
        (choice gs) s
    in
    g


let subtract_size
    (type a)
    (g:a g)
    (m:int)
  : a g =
  let subtracted_gen
      (s:int)
    : a option =
    let new_size = s - m in
    if new_size < 1 then
      None
    else
      g (s-m)
  in
  subtracted_gen

let product
    (type a)
    (gs:a g list)
  : a list g =
  let len = List.length gs in
  let list_gen
      (s:int)
    : a list option =
    let s = if len = 0 then 0 else s / len in
    let gs = List.map ~f:(fun g -> g s) gs in
    distribute_option gs
  in
  list_gen

let map
    (type a)
    (type b)
    ~(f:a -> b)
    (g:a g)
  : b g =
  (Option.map ~f) % g

let size_seq
  ()
  : int Sequence.t =
  Quickcheck.random_sequence Quickcheck.Generator.size

let of_list
    (type a)
    (l:a list)
  : a g =
  fun _ ->
    let i = Random.int (List.length l) in
    Some (List.nth_exn l i)

let g_to_seq
    (type a)
    (g:a g)
  : a Sequence.t =
  let size_seq = size_seq () in
  Sequence.unfold_step
    ~init:size_seq
    ~f:(fun size_seq ->
        let (size,size_seq) = Option.value_exn (Sequence.next size_seq) in
        begin match g size with
          | None -> Skip size_seq
          | Some v -> Yield (v,size_seq)
        end)

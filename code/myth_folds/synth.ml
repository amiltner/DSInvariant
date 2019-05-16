open Core
open Consts
open Lang
open Printf
open Rtree
open Sigma

type synth_step =
  | SynthSaturate of float      (* Try to saturate e-guesses *)
  | SynthGrowMatches            (* Increase the depth of matches *)
  | SynthGrowScrutinees of int  (* Grow the scrutinees of all matches *)

type synth_plan = synth_step list

let standard_synth_plan : synth_plan =
  [ SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthGrowScrutinees 2
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthGrowMatches
  ; SynthGrowScrutinees 4
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthGrowScrutinees 4
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthGrowScrutinees 3
  ; SynthSaturate 0.24
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees 5
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees 5
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees 5
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees 5
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees 5
  ; SynthSaturate 0.25
  ]

let saturate_guesses (timeout:float) ?short_circuit:(sc = true) (s:Sigma.t) (env:env) (t:rtree) (condition:exp -> Float.t) =
  let rec update n =
    print_endline (string_of_int n);
    if n <= !max_eguess_size then begin
      Timing.record
        ~label:"saturate_guesses::update_exps"
        ~action:(fun _ -> update_exps ~short_circuit:sc timeout s env t);
      Timing.record
        ~label:"saturate_guesses::propogate_exps"
        ~action:(fun _ -> propogate_exps ~short_circuit:sc condition t |> ignore);
      update (n+1)
    end
  in
    update 1

let execute_synth_step
    (s:Sigma.t)
    (env:env)
    (t:rtree)
    (st:synth_step)
    (condition:exp -> Float.t)
  : exp option =
  reset_timeouts t;
  begin match st with
  | SynthSaturate timeout -> begin
      do_if_verbose (fun _ ->
        printf "Saturating E-guesses (timeout = %.2f)...\n%!" timeout);
      Timing.record
        ~label:"synth::saturate_guesses"
        ~action:(fun _ -> saturate_guesses ~short_circuit:false timeout s env t condition)
    end
  | SynthGrowMatches -> begin
      do_if_verbose (fun _ -> printf "Growing matches...\n%!");
      Timing.record
        ~label:"synth::grow_matches"
        ~action:(fun _ -> grow_matches s env t)
    end
  | SynthGrowScrutinees k -> begin
      do_if_verbose (fun _ -> printf "Growing scrutinees by %d...\n%!" k);
      Timing.record
        ~label:"synth::grow_scrutinees"
        ~action:(fun _ -> grow_scrutinees s env k t)
    end
  end;
  do_if_verbose (fun _ -> printf "%s\n%!" (Rtree.pp_rtree t));
  let es =
    Timing.record
      ~label:"synth::propogate_exps"
      ~action:(fun _ -> propogate_exps ~short_circuit:false condition t)
  in
  begin match List.filter ~f:(fun e -> condition e = 1.) es with
  | [] -> None
  | e :: _ -> Some e
  end

let rec execute_synth_plan
    (s:Sigma.t)
    (env:env)
    (t:rtree)
    (plan:synth_plan)
    (condition:exp -> Float.t)
  : exp option =
  match plan with
  | [] -> None
  | st :: plan -> begin
    match execute_synth_step s env t st condition with
    | Some e -> Some e
    | None -> execute_synth_plan s env t plan condition
    end

let synthesize
    (s:Sigma.t)
    (env:env)
    (t:rtree)
    (condition:exp -> Float.t)
  : exp option =
  verbose_mode := true;
  execute_synth_plan s env t standard_synth_plan condition

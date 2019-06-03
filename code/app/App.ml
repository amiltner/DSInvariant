open Core
open Async

open DSInvGen

(*let _ = let full_spec = ProcessFile.process_full_problem problem in
  let ans =
    Verifiers.QuickCheckVerifier.implication_counter_example
      ~problem:full_spec
      ~pre:(Expr.mk_func ("x",Type.Var "t")
              (Expr.mk_app
                 (Expr.mk_app
                    (Expr.mk_var "and")
                    ((Value.to_exp (Verifiers.QuickCheckVerifier.true_val))))
                 (Value.to_exp (Verifiers.QuickCheckVerifier.true_val))
              )
              )
      ~eval:(Expr.mk_func ("x",Type.Var "t") (Expr.mk_var "x"))
      ~post:full_spec.post
  in
  begin match ans with
    | None -> failwith "Nonegrr"
    | Some anses -> print_endline (string_of_list Value.show anses)
  end*)

module EMIG = MIG.MIGLearner (EnumerativeVerifier.T) (ParSynthesizer.T)
module QCMIG = MIG.MIGLearner (QuickCheckVerifier.T) (ParSynthesizer.T)

let main (* nworkers *) filename () =
  Log.enable ~msg:"DSInfer" (Some "_log") ;
  let file_chan = Utils.get_in_channel filename in
  let problem_string = Prelude.prelude_string ^ (Stdio.In_channel.input_all file_chan)
   in Stdio.In_channel.close file_chan
    ; let problem = Parser.unprocessed_problem
          Lexer.token (Lexing.from_string problem_string)
      in print_endline (EMIG.learnInvariant ~unprocessed_problem:problem)
       ; Deferred.unit

let spec =
  Command.Spec.(
    empty
    (* +> flag "nworkers" (optional_with_default 4 int) ~doc:" Number of workers" *)
    +> anon ("filename" %: file)
  )

let () =
  Rpc_parallel.start_app
    (Command.async_spec spec main
      ~summary: "Infer a loop invariant sufficient for proving the correctness of the input problem in SyGuS format.")

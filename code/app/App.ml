open Core

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

module EMIG = MIG.Make (EnumerativeVerifier.T) (ParSynthesizer.T)
module QCMIG = MIG.Make (QuickCheckVerifier.T) (ParSynthesizer.T)

let read_accum = function
  | None -> "", ""
  | Some filename
    -> let file_chan = Utils.get_in_channel filename in
       let file_data = Stdio.In_channel.input_all file_chan
        in match String.split file_data ~on:'#' with
           | [ accum_types ; accum_annot ] -> (accum_types , accum_annot)
           | _ -> raise (DSInvGen.Exceptions.Parse_Exn "bad accumulating annotation")

let main (* nworkers *) accum_file filename () =
  Log.enable ~msg:"DSInfer" (Some "_log") ;
  let file_chan = Utils.get_in_channel filename in
  let accum_types, accum_annot = read_accum accum_file in
  let problem_string = Prelude.prelude_string ^ accum_types
                     ^ (Stdio.In_channel.input_all file_chan)
                     ^ accum_annot
   in Stdio.In_channel.close file_chan
    ; let unprocessed_problem = Parser.unprocessed_problem
                                  Lexer.token
                                  (Lexing.from_string problem_string)
      in print_endline (EMIG.learnInvariant ~unprocessed_problem)

let spec =
  Command.Spec.(
    empty
    (* +> flag "nworkers" (optional_with_default 4 int) ~doc:" Number of workers" *)
    +> flag "-a" (optional string)
            ~doc:"FILENAME accumulating annotation file"
    +> anon ("filename" %: file)
  )

let () =
  Rpc_parallel.start_app
     ~rpc_heartbeat_config:(
       Async.Rpc.Connection.Heartbeat_config.create
         ~timeout:(Time_ns.Span.of_min 3.0)
         ~send_every:(Time_ns.Span.of_sec 15.0)
    )
    (Command.basic_spec spec main
      ~summary: "Infer a representation invariant that is sufficient for proving the correctness of a module implementation.")

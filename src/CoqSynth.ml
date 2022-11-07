open ProofContext
open FileUtils

let run p_ctxt conjecture_name examples params output_type=
  let coq_synth_path = Consts.coq_synthesizer_path
  in let coq_synth_output_path = p_ctxt.dir ^ "/" ^ p_ctxt.fname ^ conjecture_name ^ "synthesis.txt"
  in 
  let funcs = String.concat "," p_ctxt.funcs
  in let examples_op = String.concat " " examples
  in let timeout_cmd = Consts.fmt "timeout  %s" !Consts.synthesizer_timeout
  in let coq_synth_cmd = Consts.fmt  "%s --logical-dir=%s --physical-dir='%s' --module=%s --type=%s --params=%s --extra-exprs=%s --examples='%s' --num-terms=%d > %s" coq_synth_path p_ctxt.namespace p_ctxt.original_dir p_ctxt.fname output_type params funcs examples_op !Consts.myth_batch_size coq_synth_output_path
  in Log.debug (Consts.fmt "CoqSynth Command is %s\n"  (Consts.fmt "%s %s" timeout_cmd  coq_synth_cmd));
  let run_myth = run_cmd (Consts.fmt "%s %s" timeout_cmd  coq_synth_cmd)
  in (List.rev (read_file coq_synth_output_path))

let enumerate_expressions (p_cxt: proof_context)
                          (conjecture_name: string)
                          (examples: string list) 
                          (var_types: (string, string) Hashtbl.t)
                          (vars: string list)
                          (output_type: string)
                          : string list =
  let input_vars, _ = 
          List.fold_left (fun (acc, ind) v -> 
                            if String.equal v Consts.synthesis_op 
                            then (acc, ind+1)
                            else 
                            (
                              if ind == (List.length vars) -1 then
                              acc ^ v ^ ":" ^ ((Hashtbl.find var_types v)), ind+1
                              else
                              acc ^ v ^ ":" ^ ((Hashtbl.find var_types v)) ^ ",", ind+1
                            )
                          ) ("",0) vars
  in let myth_op = run p_cxt conjecture_name examples input_vars output_type
in myth_op

open ProofContext
open FileUtils

let run dir fname op_fname =
  let rewrite_path = !Consts.rewriter_path
  in let timeout_cmd = Consts.fmt "timeout  %s" !Consts.synthesizer_timeout
  in let rewrite_command = Consts.fmt  "%s %s %s %s" rewrite_path dir fname op_fname
  in Feedback.msg_info (Pp.str rewrite_command);
  let run_rewrite = run_cmd (Consts.fmt "%s %s" timeout_cmd  rewrite_command)
  in run_rewrite

let generate_ml_file p_ctxt =
  let ml_extraction_file = Consts.fmt ("%s/%s") p_ctxt.dir "lfind_ml_generator.v"
  in
  let import_file = 
  Consts.fmt "%s\nFrom %s Require Import %s." (Consts.lfind_declare_module) (p_ctxt.namespace) (p_ctxt.fname)
  in let module_imports = p_ctxt.declarations
  (* List.fold_left (fun acc m -> acc ^ (m ^"\n")) "" p_ctxt.modules   *)
  in let extract_functions = List.fold_left (fun acc f -> acc ^ " " ^ f) "" p_ctxt.funcs
  in let extraction = Consts.fmt "Extraction \"%s/%s_lfind_orig.ml\" %s." p_ctxt.dir p_ctxt.fname extract_functions
  
  in let ml_extract_content = Consts.fmt ("%s\n%s\n%s\n%s\n%s\n%s\n%s\n%s\n") Consts.lfind_declare_module import_file module_imports Consts.extraction_import Consts.extract_nat Consts.extract_list extraction Consts.vernac_success
  
  in FileUtils.write_to_file ml_extraction_file ml_extract_content;
  let cmd = Consts.fmt "coqc -R %s/ %s %s" p_ctxt.dir p_ctxt.namespace ml_extraction_file
  in FileUtils.run_cmd cmd
  
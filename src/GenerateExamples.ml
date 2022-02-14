open ProofContext

let construct_data_collection vars typs hyps = 
  let examples = String.concat " ++ \"|\" ++ " @@
    List.map (fun v -> Consts.fmt ("\"%s:\" ++ \"(\" ++ show %s ++ \")\"") v v) vars
  in let hyps_string = List.fold_left (fun acc v -> acc ^ " " ^ v) "" hyps
  in let func_signature = Consts.fmt ("Definition collect_data (dummy:nat) %s :=\n") hyps_string
  in Consts.fmt ("%s let lfind_var := %s\n in let lfind_v := print dummy lfind_var\n in lfind_state lfind_v %s.\n")
  func_signature examples hyps_string

let lfind_extract_examples p_ctxt =
let lfind_content = "
let write_to_file value=
  let oc = open_out_gen [Open_append; Open_creat] 0o777 \""^p_ctxt.dir ^"/examples_" ^  p_ctxt.fname ^ ".txt\" in
  Printf.fprintf oc \"%s\\n\"  value;
  close_out oc; ()
let print n nstr=
  write_to_file (String.of_seq (List.to_seq nstr));
  (n)
  "
in let extract_file_name = Consts.fmt ("%s/%s") p_ctxt.dir "extract.ml"
in FileUtils.write_to_file extract_file_name lfind_content

let generate_example p_ctxt typs modules current_lemma hyps vars =
  lfind_extract_examples p_ctxt;
  let example_file = Consts.fmt ("%s/%s") p_ctxt.dir "lfind_quickchick_generator.v"
  in
  let import_file =
  Consts.fmt "From %s Require Import %s."(p_ctxt.namespace) (p_ctxt.fname)  

  in let module_imports = p_ctxt.declarations
  (* List.fold_left (fun acc m -> acc ^ (m ^"\n")) "" modules *)
  in let quickchick_import = Consts.quickchick_import
  in let qc_include = Consts.fmt ("QCInclude \"%s/\".\nQCInclude \".\".") p_ctxt.dir
  
  in let typ_derive = List.fold_left (fun acc t -> acc ^ (TypeUtils.derive_typ_quickchick t)) "" typs

  in let parameter_print = "Parameter print : nat -> string -> nat.\n"
  
  in let typ_quickchick_content = Consts.fmt ("%s\n%s\n%s\n%s\n%s\n%s\n%s\n%s\n") Consts.lfind_declare_module import_file module_imports current_lemma quickchick_import 
  qc_include Consts.def_qc_num_examples typ_derive
  in let example_print_content = Consts.fmt("%s\n%s%s")  Consts.string_scope parameter_print Consts.extract_print
  in let collect_content = construct_data_collection vars typs hyps
  in let content = typ_quickchick_content ^ example_print_content ^ collect_content ^ "QuickChick collect_data.\n" ^ Consts.vernac_success
  in FileUtils.write_to_file example_file content;
  let cmd = Consts.fmt "cd %s/ && coqc -R . %s %s" p_ctxt.dir p_ctxt.namespace example_file
  in FileUtils.run_cmd cmd
  
open ProofContext
open FileUtils

let manual_coq_to_ocaml_type typ = 
  typ
  (* if Utils.contains typ "list" then "list" else typ *)

let get_example_func examples var_types vars =
  let types = List.fold_left (fun acc v -> let updated_typ = manual_coq_to_ocaml_type (try Hashtbl.find var_types v with _ -> "")
                                            in if String.equal "" acc
                                                 then updated_typ
                                                 else acc ^ "-> " ^ updated_typ
                                 ) "" vars
  in let input_vars = List.fold_left (fun acc v -> if String.equal v Consts.synthesis_op then acc
                                                   else acc ^ " " ^ "(" ^ v ^ " : " ^ (manual_coq_to_ocaml_type (Hashtbl.find var_types v)) ^")"
                                     ) "" vars
  in let func_dec = "\nlet synth "^ input_vars ^ ": " ^ types ^ "|>\n"
  in let evidence_list = List.fold_right (fun e acc -> acc ^ "\n" ^ e) examples ""
  in let func = func_dec ^ "{\n" ^ evidence_list ^ "\n}=?"
  in func

let generate_synthesis_file p_ctxt conjecture_name examples var_types vars : string =
  let coq_ml_file = Consts.fmt "%s/%s.ml" p_ctxt.dir p_ctxt.fname
  in let lfind_file = p_ctxt.dir ^ "/" ^ p_ctxt.fname ^ conjecture_name ^ ".ml"
  in let ml_content = List.rev (FileUtils.read_file coq_ml_file)
  in let all_content = (String.concat "\n" ml_content) ^ (get_example_func examples var_types vars)
  in FileUtils.write_to_file lfind_file all_content;
  lfind_file

let get_myth_exprs myth_output =
  let val_accum = ref ""
  in List.fold_left (fun acc l -> 
                         if Utils.contains l ";;"
                         then
                         (
                            val_accum := !val_accum ^ l;
                            let updated_acc = !val_accum :: acc
                            in val_accum := "";
                            updated_acc
                         ) 
                         else
                         (
                          val_accum := !val_accum ^ "\n" ^ l;
                          acc
                         )
                 ) [] myth_output

let run synth_fname p_ctxt conjecture_name enumerate=
  let myth_path = !Consts.synthesizer_path
  in let myth_output_path = p_ctxt.dir ^ "/" ^ p_ctxt.fname ^ conjecture_name ^ "synthesis.txt"
  in let timeout_cmd = Consts.fmt "timeout  %d" !Consts.synthesizer_timeout
  in let myth_cmd = Consts.fmt  "%s %s %s > %s" myth_path enumerate synth_fname myth_output_path
  in let run_myth = run_cmd (Consts.fmt "%s %s" timeout_cmd  myth_cmd)
  in get_myth_exprs (List.rev (read_file myth_output_path))

let run_parse p_ctxt fname=
  let myth_path = !Consts.synthesizer_path
  in let timeout_cmd = Consts.fmt "timeout  %d" !Consts.synthesizer_timeout
  in let parse_file = Consts.fmt "%s/%s.ml" p_ctxt.dir fname
  in let myth_cmd = Consts.fmt  "%s -parse %s" myth_path parse_file
  in
  let run_myth = run_cmd (Consts.fmt "%s %s" timeout_cmd  myth_cmd)
  in run_myth
  
let enumerate_expressions (p_cxt: proof_context)
                          (conjecture_name: string)
                          (examples: string list) 
                          (var_types: (string, string) Hashtbl.t)
                          (vars: string list)
                          (is_enum: bool) : string list =
  let synth_file = generate_synthesis_file p_cxt conjecture_name examples var_types vars
  in Log.debug (Consts.fmt "Written to synth file %s\n"  synth_file);
  let enumerate = if is_enum then "-enum" else ""
  in let myth_op = run synth_file p_cxt conjecture_name enumerate
  in myth_op

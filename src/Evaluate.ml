open ProofContext
open ExprUtils
open ExtractToML

let generate_eval_file p_ctxt eval_str : string =
  let lfind_file = p_ctxt.dir ^ "/lfind_eval.v"
  in 
  Log.debug (Consts.fmt "lfind_eval file: %s" eval_str);
  let module_imports = List.fold_left (fun acc m -> acc ^ (m ^"\n")) "" p_ctxt.modules
  in let content = Consts.fmt "%s%s\nFrom %s Require Import %s.\n%s\n%s\n%s"
                   Consts.lfind_declare_module
                   p_ctxt.declarations
                   p_ctxt.namespace 
                   p_ctxt.fname
                   ""
                   (* module_imports *)
                   Consts.coq_printing_depth
                   eval_str
  in FileUtils.write_to_file lfind_file content;
  lfind_file

let run_eval dir fname namespace =
  let cmd = "coqc -R " ^ dir ^ " " ^ namespace  ^ " " ^ fname
  in try FileUtils.run_cmd cmd with _ -> []

let get_eval_definition expr vars (var_typs:(string, string) Hashtbl.t)=
  let var_string = match Hashtbl.length var_typs with
                  | 0 -> List.fold_left (fun acc v -> acc ^ " " ^ v) "" vars 
                  | _ -> List.fold_left (fun acc v -> acc ^ " " ^ "(" ^ v ^ " : " ^ ((Hashtbl.find var_typs v)) ^")") "" vars 
  in let eval_def = "Definition lfind_eval " ^ var_string
                    ^ ":=\n"
                    ^ (Sexp.string_of_sexpr expr)
                    ^ ".\n"
  in eval_def

let get_compute_string input : string =
  "\nCompute lfind_eval " ^ input ^ ".\n"

(* Either the variable is from the original statement or it is a generalized variable which can be found from the expr mapping *)
let get_input_string vars example lfind_sigma =
  List.fold_left (fun acc v ->
                        let v_example = try (Hashtbl.find example v) 
                                        with _ -> let generalized_term,_ = (Hashtbl.find lfind_sigma v)
                                                  in (Hashtbl.find example (Sexp.string_of_sexpr generalized_term))
                        in acc ^ " " ^ v_example
                 ) "" vars

let get_evaluate_str expr vars examples lfind_sigma (var_typs:(string, string) Hashtbl.t) =
  let expr_vars = get_variables_in_expr expr [] vars
  in let eval_def = get_eval_definition expr expr_vars var_typs
  in List.fold_left (fun acc example -> let input = get_input_string expr_vars example lfind_sigma
                                        in acc ^ get_compute_string input
                    ) eval_def examples

let get_expr_vals eval_output =
  let python = "python3 "
  in let script = Consts.fmt "%sbenchmark/get_expr_vals.py"
                  !Consts.lfind_path
  in let cmd = Consts.fmt "%s %s --input=%s" python script (String.concat "\n" eval_output)
  in Log.debug (Consts.fmt "get_expr_vals cmd: %s" cmd); let run_op = FileUtils.run_cmd cmd
  in run_op

let evaluate_coq_expr expr examples p_ctxt all_vars 
(lfind_sigma:(string, Sexp.t list * string) Hashtbl.t) conj
: ((string list) * (string list)) =
  let synthesizer = !Consts.synthesizer
  in let var_typs =  match conj with
                  | None -> (Hashtbl.create 0)
                  | Some c -> ExprUtils.get_type_vars c all_vars
  in let evalstr = get_evaluate_str expr all_vars examples lfind_sigma var_typs
  in let efile = generate_eval_file p_ctxt evalstr
  in Log.debug "after generate_eval_file"; let output = run_eval p_ctxt.dir efile p_ctxt.namespace
  in Log.debug "after run_eval";
  (* TODO: Need to check here why the two outputs for COQ and ML 
     have different order. Hacky solution now!
  *)
  let coq_output  = (List.rev (get_expr_vals output))
  in Log.debug (Consts.fmt "coq_output: %s" (String.concat " " coq_output));
  let ml_output = if String.equal synthesizer "myth" then
  (
    let names, defs = get_defs_evaluated_examples coq_output
    in let ext_coqfile = generate_ml_extraction_file p_ctxt names defs
    in
    let output = run_ml_extraction p_ctxt.dir ext_coqfile p_ctxt.namespace
    in
    let ext_mlfile = Consts.fmt "%s/lfind_extraction.ml" p_ctxt.dir
    in let ext_output = List.rev (FileUtils.read_file ext_mlfile)
    in List.rev (get_ml_evaluated_examples ext_output)
  ) else [] in
  (* Log.debug (Consts.fmt "ml_output: %s" (String.concat " " ml_output)); *)
  (coq_output, ml_output)

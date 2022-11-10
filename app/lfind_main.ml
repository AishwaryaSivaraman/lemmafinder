open Constr
open Context
open Proofview.Notations
open Lfindalgo
open Sexp
open ProofContext
open Loadpath
open Loc
open Names
open LatticeUtils


exception Invalid_Examples of string
exception Invalid_MLFile of string
exception NotFound_MLFile of string
exception Rewrite_Fail of string
exception Myth_Fail of string
module SS = Set.Make(String);;


let is_ml_generation_success ml_file p_ctxt: bool= 
  if not (Sys.file_exists ml_file) then 
  (
    print_endline("Generating ML version of the .v file");
    print_endline(ml_file);
    let op = GenerateMLFile.generate_ml_file p_ctxt
    in print_endline (string_of_int (List.length op));
    let is_succ = List.fold_left (fun acc l -> acc || (Utils.contains l "lemmafinder_success") ) false op
    in is_succ
  )
  else true

let construct_state_as_lemma gl =
  let goal = Proofview.Goal.concl gl in
  let goal_vars = Utils.get_vars_in_expr goal
  in let hyps = (Utils.get_hyps (Proofview.Goal.hyps gl))
  in let all_vars = List.fold_left (fun acc (_, expr)->
  List.append acc (Utils.get_vars_in_expr expr)) goal_vars hyps
  in let var_set = Hashtbl.create (List.length all_vars)
  in List.iter (fun v -> Hashtbl.replace var_set v "") all_vars;
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let conc = (Utils.get_exp_str env sigma goal)
  in let goal = Proofview.Goal.concl gl
  in let conc_sexp = Sexp.of_string (Utils.get_sexp_compatible_expr_str env sigma goal)
  in let _, conc_atoms = (Abstract_NoDup.collect_terms_no_dup [] [] conc_sexp)
  in let c_ctxt = {env = env; sigma = sigma}
  in let atom_type_table = (update_type_table conc_atoms c_ctxt (Hashtbl.create 100))
  in let typs_from_conc = Hashtbl.fold (fun k v acc ->  if (Utils.contains v "Set") then k::acc else acc) atom_type_table []
  in
  let contanins_forall = ref false
  in let hyps, vars, typs, var_typs, hyps_str =
    List.fold_left (fun (acc_H, acc_V, acc_typs, acc_var_typs, acc_hyps_str) (v, hyp) -> 
                      let var_str = (Names.Id.to_string v)
                      in let hyp_content =  (Utils.get_exp_str env sigma hyp)
                      in let hyp_str = (Consts.fmt "(%s:%s)" var_str hyp_content)
                      in
                      let hyp_type = try TypeUtils.get_type_of_atom env sigma hyp_content
                                     with _ -> 
                                     (
                                       
                                       if Utils.contains hyp_content "forall _" then 
                                        (
                                          (* coq represents -> relation with forall _, quickchick can handle those since the quantifier is not nested *)
                                         "Prop"
                                        )
                                       else
                                       if Utils.contains hyp_content "forall" 
                                        then (print_endline "Hypotheses contains forall, Quickchick might not work!"; contanins_forall := true; "Prop")
                                        else ""
                                     ) 
                      in
                      let hyp_type = try TypeUtils.get_return_type "" (of_string ("(" ^ hyp_type ^ ")")) 
                                         with  _ -> hyp_type
                      in
                      if Utils.contains hyp_type "Prop" then
                        (hyp_str::acc_H), acc_V, acc_typs, acc_var_typs, (("(" ^ hyp_content ^ ")") :: acc_hyps_str)
                      else
                        (
                          if Utils.contains hyp_type "Set" then
                          (
                            let typ_exists = List.fold_left (fun acc t -> acc || (String.equal t hyp_content)) false acc_typs
                            in let updated_typ = match typ_exists with
                            | true -> acc_typs
                            | false -> (hyp_content::acc_typs)
                          in 
                            acc_H, (var_str::acc_V), updated_typ, (hyp_str::acc_var_typs), acc_hyps_str
                          )
                          else
                          (
                            print_endline "There is a hypothesis that is neither Set or Prop";
                            exit(0);
                            acc_H, acc_V, acc_typs, acc_var_typs, acc_hyps_str
                          )
                        )
                 ) ([],[],[],[],[]) hyps
  in
  let all_hyps = List.append var_typs hyps
  in let typs = List.fold_left (fun acc v -> 
  let typ_name = v
    (* if String.equal v "bool," then "bool" else v  *)
  in if (List.exists (String.equal typ_name) acc) then acc else typ_name::acc) typs typs_from_conc
  in if List.length all_hyps == 0 then
     (
       let var_forall = List.fold_left (fun acc v -> acc ^ " " ^ v) "forall" vars
       in if List.length vars > 0 then
       !contanins_forall, (Consts.fmt "Lemma %s:  %s, %s.\nAdmitted." Consts.lfind_lemma var_forall conc), typs, var_typs, vars, hyps_str
       else
       !contanins_forall, (Consts.fmt "Lemma %s: %s.\nAdmitted." Consts.lfind_lemma conc), typs, var_typs, vars, hyps_str
     )
    else
    (
      let vars_all = ""
        (* List.fold_left (fun acc v -> acc ^ " " ^ v)  "" vars *)
      in !contanins_forall, (Consts.fmt "Lemma %s %s %s:%s.\nAdmitted." Consts.lfind_lemma vars_all (String.concat " " all_hyps) conc), typs, var_typs, vars, hyps_str
    )
  
  (* debug = 0 if off, 1 if on;  synthesizer = synthesizer used; synth_batch_size = max size of synthesized expr; timeout = synthesizer timeout*)
let lfind_tac (debug: bool) : unit Proofview.tactic =
  Consts.start_time := int_of_float(Unix.time ());
  Log.is_debug := debug;
  Consts.synth_batch_size := int_of_string !Opts.synth_batch_size;
  Consts.synthesizer := !Opts.synthesizer;
  Consts.synthesizer_timeout := int_of_string !Opts.timeout;
  Proofview.Goal.enter
  begin fun gl ->
    print_endline("The synthesizer used is " ^ !Consts.synthesizer ^ " with myth batch size " ^ string_of_int !Consts.synth_batch_size);
    let is_running = Utils.get_env_var "is_lfind"
    in 
    if String.equal is_running "true" then Tacticals.New.tclZEROMSG (Pp.str ("LFind is already running! Aborting"))
    else
      begin
        Utils.env_setup ();
        let contanins_forall, curr_state_lemma, typs, var_typs, vars, hyps = construct_state_as_lemma gl
        in print_endline curr_state_lemma;
        let p_ctxt, c_ctxt = construct_proof_context gl
        in Log.stats_log_file := p_ctxt.dir ^ Consts.log_file;
        Log.error_log_file := p_ctxt.dir ^ Consts.error_log_file;
        Log.stats_summary_file := p_ctxt.dir ^ Consts.summary_log_file;
        let module_names =
          Utils.get_modules (p_ctxt.dir ^ "/" ^ p_ctxt.fname ^ ".v")
        in
        let p_ctxt = {p_ctxt with modules = module_names; types = typs; hypotheses = hyps; all_vars = vars}
        (* If myth is chosen as the synthesizer, generate .ml file and check if it is parsable by myth *)
        in
        if String.equal !Consts.synthesizer "myth" then
        (
          let ml_file = Consts.fmt "%s/%s_lfind_orig.ml" p_ctxt.dir p_ctxt.fname
          in 
          (
          let is_success = is_ml_generation_success ml_file p_ctxt
          in
          if not is_success then raise (Invalid_MLFile "Failed Generating .ml of the .v file") else 
          (
            if not (Sys.file_exists ml_file) then raise (NotFound_MLFile ".ml file of .v not found")
            else
            (* Now call the library to rewrite the ast *)
            let run_op = GenerateMLFile.run p_ctxt.dir (p_ctxt.fname^"_lfind_orig") p_ctxt.fname
            in let is_success = List.fold_left (fun acc l -> acc || (Utils.contains l "rewrite_success") ) false run_op
            in if not is_success then raise (Rewrite_Fail "AST rewriting of .ml file failed!") else
            (
              let run_op = Myth.run_parse p_ctxt (p_ctxt.fname^"_wsynth")
              in let is_exception = List.fold_left (fun acc l -> acc || (Utils.contains l "exception") ) false run_op
              in if is_exception then raise (Myth_Fail "Myth failed to parse .ml file!") else
              Feedback.msg_info (Pp.str "lemmafinder_ml_generation_success");
            )
          )        
          );
        );
        
        (* if example file exists use it, else generate examples *)
        let example_file = Consts.fmt "%s/examples_%s.txt" p_ctxt.dir p_ctxt.fname
        in 
        if not (Sys.file_exists example_file) && (List.length vars) > 0 then 
        (
          print_endline "Example file not found, generating";
          if contanins_forall then (print_endline ("Contains forall, and no example file provided. Quickchick does not work with forall"); exit(0);)
          else
          (
            let op = GenerateExamples.generate_example p_ctxt typs module_names curr_state_lemma var_typs vars
            in print_endline (string_of_int (List.length op));
            let is_success = List.fold_left (fun acc l -> acc || (Utils.contains l "lemmafinder_success") ) false op
            in
            if not is_success then raise (Invalid_Examples "Quickchick failed to generate examples!") else 
            Feedback.msg_info (Pp.str "lemmafinder_example_generation_success")
          )
        );
        
        let coq_examples = Examples.dedup_examples (FileUtils.read_file example_file)
        in LogUtils.write_tbl_list_to_log coq_examples "Coq Examples";
        let ml_examples = if String.equal !Consts.synthesizer "myth" then
        (
          Examples.get_ml_examples coq_examples p_ctxt
        ) else coq_examples
        in LogUtils.write_tbl_list_to_log ml_examples "ML Examples";
        let op = FileUtils.run_cmd "export is_lfind=true"
        in let abstraction = Abstract_NoDup.abstract
        in let generalized_terms, conjectures = abstraction p_ctxt c_ctxt
        in 
        (* create a coq file that has the current stuck state a prover can use *)
        let curr_state_lemma_file = Consts.fmt "%s/%s.v" p_ctxt.dir Consts.lfind_lemma
        in let content = Consts.fmt "%s%s\nFrom %s Require Import %s.\n %s"
                         Consts.lfind_declare_module
                         p_ctxt.declarations
                         p_ctxt.namespace
                         p_ctxt.fname
                         curr_state_lemma
        in FileUtils.write_to_file curr_state_lemma_file content;
        Consts.lfind_lemma_content := content;

        (* get ml and coq version of the output of generalized terms *)
        let coq_examples, ml_examples = (ExampleUtils.evaluate_terms generalized_terms coq_examples ml_examples p_ctxt)
        in 
        List.iter (fun c -> LogUtils.write_tbl_to_log c "COQE") coq_examples;
        
        let valid_conjectures, invalid_conjectures = (Valid.split_as_true_and_false conjectures p_ctxt)
        in
        let hyp_conjectures = Hypotheses.conjectures_with_hyp invalid_conjectures p_ctxt
        in 
        let hypo_valid_conjectures, _ = (Valid.split_as_true_and_false hyp_conjectures p_ctxt)
        in
        Log.debug (Consts.fmt "no of valid conjectures with hypotheses is %d" (List.length hypo_valid_conjectures));
        let start_time_synth = Unix.time ()
        in
        let cached_lemmas = ref (Hashtbl.create 1000)
        in let cached_exprs = ref (Hashtbl.create 1000)
        in List.iter (
          fun c ->
          let curr_time = int_of_float(Unix.time ())
          in let elapsed_time = curr_time - int_of_float(start_time_synth)
          in print_endline (string_of_int elapsed_time);
          if elapsed_time < 5100 then
          (print_endline c.conjecture_name;
          Log.debug (Consts.fmt "Cache size is %d\n" (Hashtbl.length !cached_lemmas));
          (Synthesize.synthesize cached_exprs cached_lemmas p_ctxt ml_examples coq_examples c);)
          else ()
        )
        invalid_conjectures ;
        Log.debug ("Completed Synthesis");
        Stats.summarize !Stats.global_stat curr_state_lemma;
        Log.debug ("COMPLETED LFIND SYNTHESIZER");

        Tacticals.New.tclZEROMSG (Pp.str ("LFIND Successful."))
      end
  end 

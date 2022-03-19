open Stdlib
open FileUtils

let scrape_data prelude proverbot fname =
  let python = "python3 " 
  in let script = proverbot ^ "src/scrape.py "
  in let cmd = python ^ script ^ "--prelude="^ prelude ^ " " ^ fname ^" -P"
  in let run_op = run_cmd cmd
  in ()

let search prelude proverbot fname axiom_opt =
  Random.self_init ();
  let rnd_str = Utils.gen_rand_str 12
  in
  let python = "python3 "
  in let script = proverbot ^ "src/search_file.py "
  in let weights_file  = proverbot ^"data/polyarg-weights.dat "
  in let cmd = Consts.fmt "%s %s --prelude=%s --weightsfile=%s %s %s -P -o %s/search-report-%s --max-search-time-per-lemma=10.0" python script prelude weights_file fname axiom_opt prelude rnd_str
  in let run_op = run_cmd cmd
  in Log.debug(List.fold_left (fun acc c -> acc ^ (Consts.fmt "Line from stdout: %s\n" c)) "" run_op);
  Consts.fmt "search-report-%s" rnd_str

let output_code prelude conjecture_names report_name: (string, bool) Hashtbl.t =
  let code_tbl = Hashtbl.create (List.length conjecture_names)
  in List.iter (fun c -> 
  let cmd = "cat " ^ prelude ^"/" ^ report_name ^ "/*-proofs.txt | grep SUCCESS | grep " ^ c ^ " -c"
  in let cmd_op = run_cmd cmd
  in let code = (if cmd_op = [] 
      then false 
      else
      (match List.hd cmd_op with
      | "0" -> false
      | "1" -> true
      | _ -> false))
  in Hashtbl.add code_tbl c code;) conjecture_names;
  code_tbl

let remove_current_search prelude =
  let cmd = "rm -rf " ^ prelude ^ "/search-report*"
  in let cmd_op = run_cmd cmd
  in ()

let run prelude proof_names fname axiom_fname  : (string, bool) Hashtbl.t =
  let axiom_opt = if String.equal axiom_fname "" then "" else "--add-axioms=" ^ axiom_fname
  in let report_folder = search prelude !Consts.prover_path fname axiom_opt
  in let code_tbl = (output_code prelude proof_names report_folder)
  in 
  LogUtils.write_bool_tbl_to_log code_tbl "Proverbot run output";
  code_tbl
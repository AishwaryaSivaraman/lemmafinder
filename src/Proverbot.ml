open Stdlib
open FileUtils

let scrape_data prelude proverbot fname =
  let python = "python3 " 
  in let script = proverbot ^ "src/scrape.py "
  in let cmd = python ^ script ^ "--prelude="^ prelude ^ " " ^ fname ^" -P"
  in let run_op = run_cmd cmd
  in ()

let search prelude proverbot fname axiom_opt conjecture_name =
  Random.self_init ();
  let rnd_str = Utils.gen_rand_str 6
  in
  let python = "python3 "
  in let script = proverbot ^ "src/search_file.py "
  in let weights_file  = proverbot ^"data/polyarg-weights.dat "
  in let cmd = Consts.fmt "timeout 30 %s %s --prelude=%s --weightsfile=%s %s %s --no-generate-report --max-proof-time=15 -P -o %s/search-report-%s-%s" python script prelude weights_file fname axiom_opt prelude conjecture_name rnd_str
  in let run_op = run_cmd cmd
  in Log.debug(List.fold_left (fun acc c -> acc ^ (Consts.fmt "Line from stdout: %s\n" c)) "" run_op);
  Consts.fmt "search-report-%s-%s" conjecture_name rnd_str

let output_code prelude conjecture_name report_name: bool =
  let cmd = "cat " ^ prelude ^"/" ^ report_name ^ "/*-proofs.txt | grep SUCCESS | grep " ^ conjecture_name ^ " -c"
  in let cmd_op = run_cmd cmd
  in if cmd_op = [] 
      then false 
      else
      (match List.hd cmd_op with
      | "0" -> false
      | "1" -> true
      | _ -> false)

let remove_current_search prelude =
  let cmd = "rm -rf " ^ prelude ^ "/search-report*"
  in let cmd_op = run_cmd cmd
  in ()

let run prelude proof_name fname axiom_fname : bool =
  if !Opts.enable_proverbot then
    let axiom_opt = if String.equal axiom_fname "" then "" else "--add-axioms=" ^ axiom_fname
    in let report_folder = search prelude !Consts.prover_path fname axiom_opt proof_name
    in let code = (output_code prelude proof_name report_folder)
    in Log.debug(Consts.fmt "Code for conjecture %s is %b\n" proof_name code);
    code
  else
    false
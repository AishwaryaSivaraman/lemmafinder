open Stdlib
open FileUtils

let scrape_data prelude proverbot fname =
  let python = "python3 " 
  in let script = proverbot ^ "src/scrape.py "
  in let cmd = python ^ script ^ "--prelude="^ prelude ^ " " ^ fname ^" -P"
  in let run_op = run_cmd cmd
  in ()

let search prelude proverbot fname axiom_opt=
  let python = "python3 " 
  in let script = proverbot ^ "src/search_file.py "
  in let weights_file  = proverbot ^"data/polyarg-weights.dat "
  in let cmd = Consts.fmt "timeout 10 %s %s --prelude=%s --weightsfile=%s --no-generate-report %s %s -P -o %s/search-report" python script prelude weights_file fname axiom_opt prelude
  in let run_op = run_cmd cmd
  in Log.debug(List.fold_left (fun acc c -> acc ^ (Consts.fmt "Line from stdout: %s\n" c)) "" run_op)

let output_code prelude conjecture_name : bool =
  let cmd = "cat " ^ prelude ^"/search-report/*-proofs.txt | grep SUCCESS | grep " ^ conjecture_name ^ " -c"
  in let cmd_op = run_cmd cmd
  in if cmd_op = [] 
      then false 
      else
      (match List.hd cmd_op with
      | "0" -> false
      | "1" -> true
      | _ -> false)

let remove_current_search prelude =
  let cmd = "rm -rf " ^ prelude ^ "/search-report"
  in let cmd_op = run_cmd cmd
  in ()

let run prelude proof_name fname axiom_fname : bool =
  remove_current_search prelude;
  let axiom_opt = if String.equal axiom_fname "" then "" else "--add-axioms=" ^ axiom_fname
  in search prelude !Consts.prover_path fname axiom_opt;
  let code = (output_code prelude proof_name)
  in Log.debug(Consts.fmt "Code for conjecture %s is %b\n" proof_name code);
  code
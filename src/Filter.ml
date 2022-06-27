open LatticeUtils

exception Mismatch_Filtered of string

let run lemmas imports prelude theorem_name theorem = 
  let python = "python3 "
  in let script = Consts.fmt "%sbenchmark/filter.py"
                  !Consts.lfind_path
  in let cmd = Consts.fmt "%s %s --prelude=%s --theorem_name=\"%s\" --theorem=\"%s\" --lemmas %s --imports %s"
               python
               script
               prelude
               theorem_name
               theorem
               lemmas
               imports
  in let run_op = FileUtils.run_cmd cmd
  in run_op


let name_in_lst name lst =
  let name = String.trim name
  in List.fold_left (fun acc (n, conj) ->
                      if String.equal name (String.trim n)
                      then (true, conj)
                      else acc
                    ) (false, "") lst


let filter_lemmas conjectures
                  imports
                  prelude
                  theorem_name
                  theorem
                  : (string * conjecture) list * string * string
                  =
  let lemmas = List.fold_left (fun acc (_,c) -> acc ^ " \"" ^ c.conjecture_str ^ "\"") "" conjectures
  in let run_op = run lemmas imports prelude theorem_name theorem
  in List.iter print_endline run_op;
  let simplified_lemmas, trivial_count, is_version_count = List.fold_left (
                     fun (acc, t_count, v_count) l ->
                      if Utils.contains l ":trivial_count" then
                      acc, List.hd (String.split_on_char ':' l), v_count
                      else
                      (
                       if Utils.contains l ":is_version_count" then
                       acc, t_count,List.hd (String.split_on_char ':' l) 
                      else
                        (
                          if Utils.contains l "FilteredLemma$" 
                          then
                            let content = String.split_on_char '$' l
                            in (List.nth content 1,List.nth content 2) :: acc, t_count, v_count 
                          else
                            acc,t_count,v_count
                        )
                      )
                    ) ([],"","") run_op
  in
  let simplified_conjectures = List.fold_left 
              (fun acc (s, c) ->
                              let is_match, conj = name_in_lst c.conjecture_name simplified_lemmas
                              in
                              if is_match
                              then (s,{c with body=conj;}) :: acc
                              else acc
              ) [] conjectures
  in
  if (List.length simplified_lemmas) != (List.length simplified_conjectures)
  then raise @@ Mismatch_Filtered ("Filtered lemmas do not match the result")
  else simplified_conjectures, trivial_count, is_version_count
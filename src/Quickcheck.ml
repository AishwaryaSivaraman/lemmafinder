open FileUtils

let quickcheck fname namespace dir =
  let cmd = Consts.fmt "coqc -R %s %s %s" dir namespace fname
  in run_cmd cmd

let output_code (op: string list)
                : bool * string list =
  let last_line = try List.hd (List.rev op)
                  with _ -> Log.write_to_log (String.concat "\n" op) !Log.error_log_file; ""
  in Log.debug (Consts.fmt "last line is : %s" last_line);
  let is_contains = Utils.contains last_line "Passed"
  in if is_contains then true, []
  else
  (
    (*store the counterexamples*)
    let cgs, _ = List.fold_left (fun (acc, is_acc) l -> 
                                      if  Utils.contains l ".native" then acc, true 
                                      else
                                      (
                                        if Utils.contains l "Failed" then acc, false
                                        else (
                                              if is_acc then (List.append acc [l]), is_acc
                                              else acc, is_acc
                                            )
                                      )
                                ) ([],false) op
    in false, cgs
  )
  

let run (fname: string) (namespace: string) (dir: string)
        : bool * string list =
  if !Opts.enable_quickchick then
    (output_code (quickcheck fname namespace dir))
  else
    (false, [])

let remove_files dir =
  let cmd = "rm -rf " ^ dir ^ "/lfindconj*"
  in let cmd_op = run_cmd cmd
  in ()
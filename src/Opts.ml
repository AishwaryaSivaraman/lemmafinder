open Goptions

(* HYPERPARAMETERS AND RUN OPTIONS*)
let enable_quickchick = ref true
let enable_proverbot = ref true
let debug = ref false
let synthesizer = ref "coqsynth"
let synth_batch_size = ref "6"
let timeout = ref "12"

(* INFRASTRUCTURE ALLOWING FOR OPTIONS *)
(* Setting up the options for running without Quickchick *)
let _ =
  let gdopt=
    { optdepr=false;
      optkey=["Lfind";"QuickChick"];
      optname="Use QuickChick";
      optread=(fun () -> !enable_quickchick);
      optwrite=(fun b -> enable_quickchick := b)}
  in
  declare_bool_option gdopt

(* Setting up the options for running without Proverbot. *)
let _ =
  let gdopt=
    { optdepr=false;
      optkey=["Lfind";"Proverbot"];
      optname="Use Proverbot";
      optread=(fun () -> !enable_proverbot);
      optwrite=(fun b -> enable_proverbot := b)}
  in
  declare_bool_option gdopt

(* Setting up the options for running with debug. *)
let _ =
  let gdopt=
    { optdepr=false;
      optkey=["Lfind";"Debug"];
      optname="Use debugging";
      optread=(fun () -> !debug);
      optwrite=(fun b -> debug := b)}
  in
  declare_bool_option gdopt
  
(* Setting up the option to set the synthesizer. *)
let _ =
  let gdopt=
    { optdepr=false;
      optkey=["Lfind";"Synthesizer"];
      optname="Choose synthesizer";
      optread=(fun () -> !synthesizer);
      optwrite=(fun synth -> synthesizer := synth)}
  in
  declare_string_option gdopt

(* Setting up the option to set the synthesizer batch size. *)
let _ =
  let gdopt=
    { optdepr=false;
      optkey=["Lfind";"BatchSize"];
      optname="Choose the batch size";
      optread=(fun () -> !synth_batch_size);
      optwrite=(fun size -> synth_batch_size := size)}
  in
  declare_string_option gdopt

(* Setting up the option to set the synthesizer batch size. *)
let _ =
  let gdopt=
    { optdepr=false;
      optkey=["Lfind";"Timeout"];
      optname="Choose the timeout";
      optread=(fun () -> !timeout);
      optwrite=(fun time -> timeout := time)}
  in
  declare_string_option gdopt
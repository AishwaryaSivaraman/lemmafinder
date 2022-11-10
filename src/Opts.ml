open Goptions

(* HYPERPARAMETERS and RUN OPTIONS *)
let enable_quickchick = ref true
let enable_proverbot = ref true
let synthesizer = ref "coqsynth"
let synth_batch_size = ref "6"
let timeout = ref "12"

(* Can add any other parameters that you want the user to be able to set here. *)

(* Setting up option for enabling proverbot 
   To set to false: Unset Lfind Proverbot.
   To set to true: Set Lfind Proverbot. *)
let _ = 
  let gdopt = 
    {
      optdepr=false;
      optkey=["Lfind";"Proverbot"];
      optname="Use Proverbot";
      optread=(fun () -> !enable_proverbot);
      optwrite=(fun b -> enable_proverbot := b)
  }
  in declare_bool_option gdopt

(* Setting up option for enabling quickchick 
   To set to false: Unset Lfind Quickchick.
   To set to true: Set Lfind Quickchick. *)
let _ = 
  let gdopt = 
    {
      optdepr=false;
      optkey=["Lfind";"Quickchick"];
      optname="Use Quickchick";
      optread=(fun () -> !enable_quickchick);
      optwrite=(fun b -> enable_quickchick := b)
    }
  in declare_bool_option gdopt

(* Setting up option for choosing the synthesizer 
   To set: Set Lfind Synthesizer {name of synthesizer}. 
   Defaults to coqsynth*)
let _ = 
  let gdopt = 
    {
      optdepr=false;
      optkey=["Lfind";"Synthesizer"];
      optname="Choose synthesizer";
      optread=(fun () -> !synthesizer);
      optwrite=(fun synth -> synthesizer := synth)
    }
  in declare_string_option gdopt

(* Setting up option for the number of terms synthesized (batch size) 
   To set: Set Lfind Batch-Size {number of terms (k)}.
   Default to 6. *)
let _ = 
  let gdopt = 
    {
      optdepr=false;
      optkey=["Lfind";"BatchSize"];
      optname="Choose batch-size";
      optread=(fun () -> !synth_batch_size);
      optwrite=(fun k -> synth_batch_size := k)
    }
  in declare_string_option gdopt

(* Setting up option for the number of terms synthesized (batch size) 
   To set: Set Lfind Timeout {timeout (t)}.
   Default to 12. *)
let _ = 
  let gdopt = 
    {
      optdepr=false;
      optkey=["Lfind";"Timeout"];
      optname="Choose timeout";
      optread=(fun () -> !timeout);
      optwrite=(fun t -> timeout := t)
    }
  in declare_string_option gdopt
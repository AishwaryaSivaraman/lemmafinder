open Lfindalgo

let verify_synthesizer_path : bool = (Consts.coq_synthesizer_path == "coq_synth") 
let verify_proverbot_path : bool = (Utils.get_env_var Consts.prover != "")

let check_coq_synth () : string =
  match verify_synthesizer_path with
  | false -> "Synthesizer (CoqSynth) path is not set up properly."
  | true -> ""

let check_proverbot () : string =
  match verify_proverbot_path with
  | false -> "Prover (ProverBot9001) path is not set up properly; run command\"export PROVER={path to proverbot}/proverbot9001\"."
  | true -> ""
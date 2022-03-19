let lfind_declare_module = "Load LFindLoad."

let synthesis_op = "lfind_output"

let type_decl = "Type"

let debug_log_file = "/lfind_debug_log.txt"

let log_file = "/lfind_log.txt"

let summary_log_file = "/lfind_summary_log.txt"

let error_log_file = "/error_lfind_log.txt"

let myth_timeout = "12"

let coq_printing_depth = "Set Printing Depth 1000."

let fmt = Printf.sprintf

let extract_nat = "Extract Inductive nat => nat [ \"(O)\" \"S\" ]."

let extract_list = "Extract Inductive list => list [ \"Nil\" \"Cons\" ]."

let lfind_lemma = "lfind_state"

let quickchick_import = "From QuickChick Require Import QuickChick."

let string_scope = "Open Scope string_scope.\n"

let extract_print = "Extract Constant print => \"Extract.print\".\n"

let require_extraction = "\nRequire Coq.extraction.Extraction.\nExtraction Language OCaml.\n"

let vernac_success = "Success."

let extraction_import = "Require Import Extraction."

let def_qc_num_examples = "Extract Constant defNumTests => \"50\"."

let prover = "PROVERBOT"

let synthesizer = "MYTH"

let rewriter = "REWRITE"

let prover_path = ref ""

let synthesizer_path = ref ""

let rewriter_path = ref ""

let coq_of_ocaml_path = ref ""

let lfind_path = ref ""

let myth_batch_size = 15

let time_to_category_1 = ref 0

let start_time = ref 0

let logged_time_to_cat_1 = ref false

let trivial_count = ref 0

let is_version_count = ref 0

let total_synth = ref 0

let is_false = ref 0

let is_dup = ref 0

let lfind_lemma_content = ref ""

let lfind_curr_state_lemma = ref ""
open LatticeUtils
open ProofContext
open Stats
open Consts


let term_contains_gen_var term gen_vars =
  List.exists (fun gvar -> 
                   Utils.contains (Sexp.string_of_sexpr term) gvar
              ) gen_vars

let add_synthesis_term acc gen_vars term type_tbl topconj =
  let term_type = try (Hashtbl.find type_tbl (Sexp.string_of_sexpr term)) with _ -> ""
  in let return_type = try TypeUtils.get_return_type "" (Sexp.of_string term_type) with _ -> term_type
  in 
  (* TODO: Need to ensure @eq is not added when considering variables to generalize. One way would eb check Type in return type instead of equal.*)
  if String.equal return_type type_decl
    then acc, false
    else 
        (
          let exists = List.exists (fun e -> Sexp.equal e term) acc
          in if exists 
             then acc, false
             else 
                  (* if term_contains_gen_var term gen_vars
                  then acc, false
                  else *)
                  (
                  if Sexp.equal [Expr term] topconj
                  then acc, false
                  else term :: acc, true
                  )
        )

let rec get_all_terms_to_synthesize (acc : Sexp.t list list) (conjecture: Sexp.t list)
        (gen_vars: string list) type_tbl topconj add_atoms
        : Sexp.t list list =
match conjecture with
| (Atom a) :: tl -> if add_atoms then
(
let new_acc, is_added = (add_synthesis_term acc gen_vars [Atom a] type_tbl topconj)
in get_all_terms_to_synthesize new_acc tl gen_vars type_tbl topconj add_atoms
)
else
get_all_terms_to_synthesize acc tl gen_vars type_tbl topconj add_atoms
| [Expr [Atom _; Atom _; (Expr head); Atom var]] ->
let new_acc, _ = (add_synthesis_term acc gen_vars [Atom var] type_tbl topconj)
  in let new_acc, _ = (add_synthesis_term new_acc gen_vars head type_tbl topconj)
        in get_all_terms_to_synthesize new_acc head gen_vars type_tbl topconj add_atoms
| [Expr [Atom _; Atom _; Atom var; (Expr head)]] ->
                                  let new_acc, _ = (add_synthesis_term acc gen_vars [Atom var] type_tbl topconj)
                                      in let new_acc, _ = (add_synthesis_term new_acc gen_vars head type_tbl topconj)
                                            in get_all_terms_to_synthesize new_acc head gen_vars type_tbl topconj add_atoms
| (Expr head) :: tl ->
 (
  let new_acc, is_added = (add_synthesis_term acc gen_vars head type_tbl topconj)
  in let head_terms = get_all_terms_to_synthesize new_acc head gen_vars type_tbl topconj add_atoms
  in get_all_terms_to_synthesize head_terms tl gen_vars type_tbl topconj add_atoms
 )
| [] -> acc
(* 
   We pick terms based on the size. 
   Add the largest expression that can be replaced for synthesis. 
*)
let rec get_terms_to_synthesize (acc : Sexp.t list list)
                                (conjecture: Sexp.t list)
                                (gen_vars: string list)
                                (type_tbl: (string, string) Hashtbl.t)
                                (topconj: Sexp.t list)
                                (add_atoms: bool)
                                : Sexp.t list list =
  match conjecture with
  | (Atom a) :: tl -> if add_atoms then
                      (
                        let new_acc, is_added = (add_synthesis_term acc gen_vars [Atom a] type_tbl topconj)
                        in get_terms_to_synthesize new_acc tl gen_vars type_tbl topconj add_atoms
                      ) 
                      else
                        get_terms_to_synthesize acc tl gen_vars type_tbl topconj add_atoms
  | [Expr [Atom _; Atom _; (Expr head); Atom var]] -> let new_acc, _ = (add_synthesis_term acc gen_vars [Atom var] type_tbl topconj)
  in let new_acc, _ = (add_synthesis_term new_acc gen_vars head type_tbl topconj)
  in new_acc
  | (Expr head) :: tl ->
                         (
                          let new_acc, is_added = (add_synthesis_term acc gen_vars head type_tbl topconj)
                          in if is_added then
                          get_terms_to_synthesize new_acc tl gen_vars type_tbl topconj add_atoms
                          else 
                          (
                            let head_terms = get_terms_to_synthesize new_acc head gen_vars type_tbl topconj add_atoms
                            in get_terms_to_synthesize head_terms tl gen_vars type_tbl topconj add_atoms
                          )
                         )
  | [] -> acc

let add_conj_vars conj_vars vars lfind_vars var =
let is_exists_in_vars = List.exists (fun v -> String.equal v var) vars
in let is_exists_in_lfind_vars = List.exists (fun v -> String.equal v var) lfind_vars
in let is_dup = List.exists (fun v -> String.equal v var) conj_vars
in if (is_exists_in_vars || is_exists_in_lfind_vars) & not is_dup 
    then var :: conj_vars
    else conj_vars

let rec get_variables_except_expr conjecture expr conj_vars vars lfind_vars =
match conjecture with
| (Sexp.Atom v) :: tl -> 
                        let updated_vars = (add_conj_vars conj_vars vars lfind_vars v)
                        in get_variables_except_expr tl expr updated_vars vars lfind_vars
| (Sexp.Expr hd) :: tl -> 
                          if (Sexp.equal hd expr)
                          then
                            get_variables_except_expr tl expr conj_vars vars lfind_vars
                          else
                            (let head_vars = get_variables_except_expr hd expr conj_vars vars lfind_vars
                            in get_variables_except_expr tl expr head_vars vars lfind_vars)
| [] -> conj_vars

let get_quantified_var var_types =
  let normalized_vars = Hashtbl.create (Hashtbl.length var_types)
  in let count = ref 0
  in (Hashtbl.fold (fun k v (acc, acc_vars) ->
                               let new_var = Sexp.get_normalized_var_name !count
                               in count := !count + 1;
                               Hashtbl.add normalized_vars k new_var;
                               if String.equal k synthesis_op
                               then acc, acc_vars
                               else acc ^ " " ^ "(" ^ new_var ^ " : " ^ v ^ ")", (List.append acc_vars [k])
                  ) var_types ("", [])), normalized_vars

let get_synthesis_conjecture is_equal_conj op_type curr_synth_term conjecture var_types counter synthesized_expr =
  Log.debug (Consts.fmt "synth term is %s" (Sexp.string_of_sexpr curr_synth_term));
  Log.debug (Consts.fmt "synthesized expression is %s" synthesized_expr);
  let synthesis_body = if not is_equal_conj then
                       (Sexp.of_string (Sexp.replace_sub_sexp conjecture.body_sexp curr_synth_term synthesized_expr))
                       else
                       (Sexp.of_string (Consts.fmt "(@eq %s (%s) (%s))"  op_type (Sexp.string_of_sexpr curr_synth_term) synthesized_expr))
  in
  let var_strs, norm_vars, normalized_vars = Sexp.normalize_sexp synthesis_body var_types
  in
  let synthesized_expr = "(" ^ synthesized_expr ^ ")"
  in
  let replaced_conj = Sexp.normalize_sexp_vars synthesis_body normalized_vars
  in
  let conj_prefix = 
  if is_equal_conj then
    conjecture.conjecture_name ^ "eqsynth"
  else 
    conjecture.conjecture_name ^ "synth"
  in let synth_conj_name = LatticeUtils.gen_conjecture_name conj_prefix counter
  in let synth_conj = synth_conj_name ^ " " ^ ": forall " ^ var_strs ^ ", " ^ replaced_conj
  in Log.debug (Consts.fmt "replaced conjecture is %s" synth_conj);
  let synthesis_conjecture = {
                                  sigma = conjecture.sigma;
                                  conjecture_str = synth_conj;
                                  body = replaced_conj;
                                  conjecture_name = synth_conj_name;
                                  body_sexp = (Sexp.of_string replaced_conj);
                                  lfind_vars = conjecture.lfind_vars;
                                  all_expr_type_table = Hashtbl.create 0;
                                  atom_type_table = var_types;
                                  hyps = conjecture.hyps;
                                  cgs = [];
                                  vars = norm_vars;
                                  vars_with_types = var_strs;
                                  normalized_var_map = normalized_vars;
                                }
  in synthesized_expr, synthesis_conjecture

let filter_cached_lemmas conjectures cached_lemmas =
  List.filter (fun (s, conj) ->
    if (Hashtbl.mem cached_lemmas conj.body)
      then false
      else (Hashtbl.replace cached_lemmas conj.body true; true)
  ) conjectures

let filter_valid_conjectures synthesized_conjectures p_ctxt original_conjecture =
  let n_cores = (Utils.cpu_count () / 2)
  in Parmap.parmap ~ncores:n_cores (fun (s, conj) ->
                      (
                        (
                          let is_valid, cgs = Valid.check_validity conj p_ctxt
                          in (s, conj, is_valid, cgs)
                         )
                      )
                  ) (Parmap.L synthesized_conjectures)


let filter_provable_conjectures valid_conjectures p_ctxt original_conjecture =
  let n_cores = (Utils.cpu_count () / 2)
  in Parmap.parmap ~ncores:1
  (fun (s, conj) -> let is_provable = (Provable.check_lfind_theorem_add_axiom p_ctxt conj.conjecture_name conj.conjecture_str)
  in s, conj, is_provable) (Parmap.L valid_conjectures)

let get_vars_for_equal_synthesis conjecture curr_synth_term vars all_vars=
  let vars_for_synthesis = ExprUtils.get_variables_in_expr curr_synth_term [] all_vars
  in vars_for_synthesis

let get_vars_for_synthesis conjecture curr_synth_term vars all_vars = 
  let vars_for_synthesis = (get_variables_except_expr conjecture.body_sexp curr_synth_term [] vars conjecture.lfind_vars)
  in let vars_for_synthesis = if Int.equal (List.length vars_for_synthesis) 0 then
                              (* the case when we make the entire conjecture a hole *)
                              ExprUtils.get_variables_in_expr conjecture.body_sexp [] all_vars
                            else vars_for_synthesis
  in vars_for_synthesis

let enumerate_conjectures conjecture curr_synth_term vars_for_synthesis p_ctxt ml_examples output_examples synth_count is_equal_conj = 
  let var_types = ExprUtils.get_type_vars conjecture vars_for_synthesis
  in
  let subst_synthesis_term = ExprUtils.subst_lfind_vars_in_expr curr_synth_term conjecture.sigma
  in 
  (* Sometimes the subst_synthesis_term can have () or not around the expression, so when lookup fails we are going to take the expr within () TODO: This is a hack, need to check why all_expr_type_table table didnt include ()*)
  let output_type = try (Hashtbl.find conjecture.all_expr_type_table subst_synthesis_term)  
  with _ -> (Hashtbl.find conjecture.all_expr_type_table (String.sub subst_synthesis_term 1 ((String.length subst_synthesis_term) -2)))  
  in 
  let output_type = ( try TypeUtils.get_return_type "" (Sexp.of_string output_type) with _ -> output_type)
  in Hashtbl.add var_types synthesis_op output_type;
  let myth_examples = Examples.gen_synthesis_examples ml_examples output_examples vars_for_synthesis conjecture.sigma
  in LogUtils.write_list_to_log myth_examples (!Consts.synthesizer ^ " examples");
  
  let vars_for_synthesis = List.append vars_for_synthesis [synthesis_op]
  in let conjecture_name = (conjecture.conjecture_name ^ string_of_int(Utils.next_val synth_count ())) in
  let enumerated_exprs = if String.equal !Consts.synthesizer "myth" then
    (
      let enumerated_myth_exprs = Myth.enumerate_expressions p_ctxt conjecture_name  myth_examples var_types vars_for_synthesis true
      in 
      let start_i = 0 
      in let end_i = start_i + Consts.myth_batch_size
      in let top_k = Utils.slice_list start_i end_i enumerated_myth_exprs
      in CoqofOcaml.get_coq_exprs top_k p_ctxt conjecture_name
    ) else (
      CoqSynth.enumerate_expressions p_ctxt conjecture_name myth_examples var_types vars_for_synthesis output_type
    )
  in
  let counter = ref 0
  in let synthesized_conjectures = List.map (get_synthesis_conjecture is_equal_conj output_type curr_synth_term conjecture var_types (Utils.next_val counter))enumerated_exprs
  in synthesized_conjectures, enumerated_exprs

let get_filtered_conjectures conjectures p_ctxt conjecture cached_lemmas =
  let filtered_valid_conjectures = filter_valid_conjectures conjectures p_ctxt conjecture
  in List.fold_right (
                      fun (s, conj, is_valid, cgs) (acc, inv_acc) ->
                        if is_valid then
                        (
                          (s,conj)::acc, inv_acc
                        )
                        else
                        (
                          Hashtbl.replace !cached_lemmas conj.body is_valid;
                          acc, {conj with cgs = cgs}::inv_acc
                        )
                      ) filtered_valid_conjectures ([], [])  

let synthesize_lemmas 
                      (synth_count: int ref)
                      (conjecture: conjecture)
                      (ml_examples: (string, string) Hashtbl.t list)
                      (coq_examples: (string, string) Hashtbl.t list)
                      (p_ctxt: proof_context)
                      (cached_lemmas: (string, bool) Hashtbl.t ref)
                      (cached_exprs: (string, bool) Hashtbl.t ref)
                      (curr_synth_term: Sexp.t list)
                      : synthesis_stat =
  let synthesizer = !Consts.synthesizer
  in let input_examples = if String.equal synthesizer "myth" then ml_examples else coq_examples
  in Log.debug (Consts.fmt "Synth term is %s\n" (Sexp.string_of_sexpr curr_synth_term));
  let all_vars = List.append p_ctxt.vars conjecture.lfind_vars
  in let coq_output_examples, ml_output_examples = (Evaluate.evaluate_coq_expr curr_synth_term coq_examples p_ctxt all_vars conjecture.sigma (Some conjecture))
  in 
  let vars_for_synthesis = get_vars_for_synthesis conjecture curr_synth_term p_ctxt.vars all_vars
  in
  let output_examples = 
  if String.equal synthesizer "myth" then
    ml_output_examples
  else 
    coq_output_examples
  in
  let synthesized_conjectures, enumerated_exprs = enumerate_conjectures conjecture curr_synth_term vars_for_synthesis p_ctxt input_examples output_examples synth_count false

  in let expr_found = try
  let _ = (Hashtbl.find !cached_exprs (Sexp.string_of_sexpr curr_synth_term))
  in true
  with _ -> false
  in let synthesized_conjectures, enumerated_exprs = if expr_found then synthesized_conjectures, enumerated_exprs else
  (
  Log.debug (Consts.fmt "the equal synthesis term is %s" (Sexp.string_of_sexpr curr_synth_term));
  let vars_for_synthesis = get_vars_for_equal_synthesis conjecture curr_synth_term p_ctxt.vars all_vars
  in 
  LogUtils.write_list_to_log vars_for_synthesis "equal vars for synthesis";
  let equal_synthesized_conjectures, equal_enumerated_exprs = enumerate_conjectures conjecture curr_synth_term vars_for_synthesis p_ctxt input_examples output_examples synth_count true
  in Hashtbl.add !cached_exprs (Sexp.string_of_sexpr curr_synth_term) true;
  (List.append synthesized_conjectures equal_synthesized_conjectures), (List.append enumerated_exprs equal_enumerated_exprs)
  )

  in Consts.total_synth := !Consts.total_synth + List.length(synthesized_conjectures);
  let filtered_conjectures = filter_cached_lemmas synthesized_conjectures !cached_lemmas
  in Consts.is_dup := !Consts.is_dup + (List.length(synthesized_conjectures) - List.length(filtered_conjectures));
  let valid_conjectures, invalid_conjectures = get_filtered_conjectures filtered_conjectures  p_ctxt conjecture cached_lemmas
  in
  let hyp_conjectures = Hypotheses.conjectures_with_hyp invalid_conjectures p_ctxt
  in
  let hyp_conjectures = List.map (fun h -> "", h) hyp_conjectures
  in let hyp_valid_conjectures, hyp_invalid_conjectures = get_filtered_conjectures hyp_conjectures  p_ctxt conjecture cached_lemmas
  in
  Log.debug (Consts.fmt "<Synthesis> no of valid conjectures with hypotheses is %d" (List.length hyp_valid_conjectures));
  let valid_conjectures =  List.append valid_conjectures hyp_valid_conjectures
  in
  Consts.is_false := !Consts.is_false + ((List.length(filtered_conjectures) + List.length(hyp_conjectures)) - List.length(valid_conjectures));

  let imports = Consts.fmt "\"%s\" %s \"From %s Require Import %s.\""
                Consts.lfind_declare_module
                (List.fold_left (fun acc d -> if (String.length d > 0) then acc ^ Consts.fmt " \"%s\"" d else acc) "" (String.split_on_char '\n' p_ctxt.declarations))
                p_ctxt.namespace
                p_ctxt.fname
  in let filter_trivial_simplify,trivial_count,is_version_count = Filter.filter_lemmas valid_conjectures imports p_ctxt.dir p_ctxt.proof_name p_ctxt.theorem
  in Consts.is_version_count := !Consts.is_version_count + int_of_string(is_version_count);
  Consts.trivial_count := !Consts.trivial_count + int_of_string(trivial_count);
  let filtered_conjectures = filter_cached_lemmas filter_trivial_simplify !cached_lemmas
  in
  Consts.is_dup := !Consts.is_dup + (List.length(filter_trivial_simplify) - List.length(filtered_conjectures));
  List.iter (fun (_,c) -> Hashtbl.replace !cached_lemmas c.body true;) filtered_conjectures;
  (* Identify synthesized lemmas that can help prove the stuck state *)
  let provable_conjectures = filter_provable_conjectures filtered_conjectures p_ctxt conjecture
  in let p_conjectures, provable_conjectures = List.fold_right (fun (s, c, is_provable) (p_acc, pro_acc) ->
      if is_provable
      then (c::p_acc, (s, c)::pro_acc)
      else (p_acc, pro_acc)
  ) provable_conjectures ([],[])
  in
  (* Identify synthesized lemmas that can prover the stuck goal, can be proven by the prover *)
  let prover_provable_conjectures, _ = Provable.split_as_provable_non_provable p_conjectures p_ctxt
  in
  let synth_stat = {
                        synthesis_term = (Sexp.string_of_sexpr curr_synth_term);
                        enumerated_exprs = enumerated_exprs;
                        valid_lemmas = filtered_conjectures;
                        original_valid_lemmas = valid_conjectures;
                        provable_lemmas = provable_conjectures;
                        prover_provable_lemmas = prover_provable_conjectures;
                      }
  in synth_stat

let synthesize cached_exprs cached_lemmas p_ctxt ml_examples coq_examples conjecture =
  Log.debug(Consts.fmt "Synthesizing for conjecture %s\n" conjecture.conjecture_str);
  Log.debug(Consts.fmt "#Coq Input Examples %d\n" (List.length coq_examples));
  (
    Log.debug (Consts.fmt "the body of sexp is %s" (Sexp.string_of_sexpr conjecture.body_sexp));
    let first_synth_terms = get_all_terms_to_synthesize [] conjecture.body_sexp conjecture.lfind_vars conjecture.all_expr_type_table conjecture.body_sexp false
    (* If there are zero synthesis expressions, we add generalized variables to synthesis *)
    in let synth_terms = if List.length first_synth_terms == 0 
                         then get_all_terms_to_synthesize [] conjecture.body_sexp conjecture.lfind_vars conjecture.all_expr_type_table conjecture.body_sexp true 
                         else first_synth_terms
    in Log.debug (Consts.fmt "Size of synth terms is %d" (List.length synth_terms));
    let sorted_synth_terms = LatticeUtils.sort_by_size synth_terms
    in let synth_count = ref (0) 
    in let synth_stats = List.map (synthesize_lemmas synth_count conjecture ml_examples coq_examples p_ctxt cached_lemmas cached_exprs) sorted_synth_terms
    in
    let gen_stat = {
                      conjecture = conjecture;
                      is_valid = false;
                      is_provable = false;
                      is_prover_provable = false;
                      synthesis_stats = synth_stats;
                      cgs = [];
                   }
    in Log.write_to_log (genstat_to_string gen_stat) !Log.stats_log_file;
    global_stat := gen_stat :: !global_stat;
    ()
  )

  
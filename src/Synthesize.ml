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

let get_normalized_var_name count =
  "lv"^(string_of_int count)

let get_quantified_var var_types =
  let normalized_vars = Hashtbl.create (Hashtbl.length var_types)
  in let count = ref 0
  in (Hashtbl.fold (fun k v acc ->
                               let new_var = get_normalized_var_name !count
                               in count := !count + 1;
                               Hashtbl.add normalized_vars k new_var;
                               if String.equal k synthesis_op
                               then acc
                               else acc ^ " " ^ "(" ^ new_var ^ " : " ^ v ^ ")"
                  ) var_types ""), normalized_vars

let get_synthesis_conjecture curr_synth_term conjecture var_types counter synthesized_expr =
  Log.debug (Consts.fmt "synth term is %s" (Sexp.string_of_sexpr curr_synth_term));
  Log.debug (Consts.fmt "synthesized expression is %s" synthesized_expr);
  let var_strs, normalized_vars = (get_quantified_var var_types)
  in let synthesized_expr = "(" ^ synthesized_expr ^ ")"
  in let replaced_conj = Sexp.normalize_sexp_vars (Sexp.of_string (Sexp.replace_sub_sexp conjecture.body_sexp curr_synth_term synthesized_expr)) normalized_vars
  in
  Log.debug (Consts.fmt "replaced conjcture is %s" replaced_conj);
  let conj_prefix = conjecture.conjecture_name ^ "synth"
  in let synth_conj_name = LatticeUtils.gen_conjecture_name conj_prefix counter
  in let synth_conj = synth_conj_name ^ " " ^ ": forall " ^ var_strs ^ ", " ^ replaced_conj
  in let synthesis_conjecture = {
                                  sigma = Hashtbl.create 0;
                                  conjecture_str = synth_conj;
                                  body = replaced_conj;
                                  conjecture_name = synth_conj_name;
                                  body_sexp = [];
                                  lfind_vars = [];
                                  all_expr_type_table = Hashtbl.create 0;
                                  atom_type_table = var_types
                                }
  in synthesized_expr, synthesis_conjecture

let filter_valid_expression enumerated_exprs conjecture_name p_ctxt original_conjecture cached_lemmas curr_synth_term var_types =
   let valid_count = ref 0 in 
   let expr_count = ref 0 in
   let counter = ref 0 in 
    List.fold_right (fun expr acc ->
                      if !valid_count > 15  or !expr_count > 200 then acc
                      else
                     (
                      expr_count := !expr_count + 1;
                       let coq_expr = (CoqofOcaml.get_coq_of_expr p_ctxt conjecture_name (!Consts.coq_of_ocaml_path) expr)
                      in
                      let s, conj = get_synthesis_conjecture curr_synth_term original_conjecture var_types (Utils.next_val counter) coq_expr
                      in 
                        (
                          let cached_output = try
                                              Some (Hashtbl.find cached_lemmas conj.body)
                                              with _ -> None
                          in match cached_output with
                          | None -> (
                                      let is_valid = Valid.check_validity conj p_ctxt
                                      in Hashtbl.add cached_lemmas conj.body is_valid;
                                      if is_valid
                                          then (valid_count := (!valid_count) + 1;
                                          (s,conj)::acc)
                                          else acc
                                    )
                          | Some (validity) -> Log.debug ("Here in cached validity check, so we do not send this back as new computation");
                                          acc
                          
                        )
                     )
                    ) enumerated_exprs []

let filter_cached_lemmas conjectures cached_lemmas = 
  List.filter (fun (s, conj) -> try
                        let _ = (Hashtbl.find cached_lemmas conj.body)
                        in false
                        with _ -> true
              ) conjectures

let filter_valid_conjectures synthesized_conjectures p_ctxt original_conjecture =
  let n_cores = (Utils.cpu_count () / 2)
  in Parmap.parmap ~ncores:n_cores (fun (s, conj) ->
                      (
                        (
                          let is_valid = Valid.check_validity conj p_ctxt
                          in (s, conj, is_valid)
                         )
                      )
                  ) (Parmap.L synthesized_conjectures)


let filter_provable_conjectures valid_conjectures p_ctxt original_conjecture =
  let n_cores = (Utils.cpu_count () / 2)
  in Parmap.parmap ~ncores:1
  (fun (s, conj) -> let is_provable = (Provable.check_lfind_theorem_add_axiom p_ctxt conj.conjecture_name conj.conjecture_str)
  in s, conj, is_provable) (Parmap.L valid_conjectures)

let synthesize_lemmas (synth_count: int ref)
                      (conjecture: conjecture)
                      (ml_examples: (string, string) Hashtbl.t list)
                      (coq_examples: (string, string) Hashtbl.t list)
                      (p_ctxt: proof_context)
                      (cached_lemmas: (string, bool) Hashtbl.t ref)
                      (curr_synth_term: Sexp.t list)  : synthesis_stat =
  
  Log.debug (Consts.fmt "Synth term is %s\n" (Sexp.string_of_sexpr curr_synth_term));
  let all_vars = List.append p_ctxt.vars conjecture.lfind_vars
  in let output_examples = []
  
  in let vars_for_synthesis = (get_variables_except_expr conjecture.body_sexp curr_synth_term [] p_ctxt.vars conjecture.lfind_vars)
  in let vars_for_synthesis = if Int.equal (List.length vars_for_synthesis) 0 then
                                (* the case when we make the entire conjecture a hole *)
                                ExprUtils.get_variables_in_expr conjecture.body_sexp [] all_vars
                              else vars_for_synthesis
  in let var_types = ExprUtils.get_type_vars conjecture vars_for_synthesis
  in
  let subst_synthesis_term = ExprUtils.subst_lfind_vars_in_expr curr_synth_term conjecture.sigma
  in 
  (* Sometimes the subst_synthesis_term can have () or not around the expression, so when lookup fails we are going to take the expr within () TODO: This is a hack, need to check why all_expr_type_table table didnt include ()*)
  let output_type = try (Hashtbl.find conjecture.all_expr_type_table subst_synthesis_term)  
  with _ -> (Hashtbl.find conjecture.all_expr_type_table (String.sub subst_synthesis_term 1 ((String.length subst_synthesis_term) -2)))  
  in 
  Hashtbl.add var_types synthesis_op ( try TypeUtils.get_return_type "" (Sexp.of_string output_type) with _ -> output_type);
  let myth_examples = []
  in LogUtils.write_list_to_log myth_examples "myth examples";
  
  let vars_for_synthesis = List.append vars_for_synthesis [synthesis_op]
  in let conjecture_name = (conjecture.conjecture_name ^ string_of_int(Utils.next_val synth_count ())) in
  let enumerated_myth_exprs = Myth.enumerate_expressions p_ctxt conjecture_name  myth_examples var_types vars_for_synthesis true
  in
  let start_i = 0 
  in let end_i = start_i + Consts.myth_batch_size
  in let top_k = Utils.slice_list start_i end_i enumerated_myth_exprs
  in let enumerated_exprs = CoqofOcaml.get_coq_exprs top_k p_ctxt conjecture_name
  in let counter = ref 0
  
  in let synthesized_conjectures = List.map (get_synthesis_conjecture curr_synth_term conjecture var_types (Utils.next_val counter))enumerated_exprs
  in Consts.total_synth := !Consts.total_synth + List.length(synthesized_conjectures);
  let filtered_conjectures = filter_cached_lemmas synthesized_conjectures !cached_lemmas
  in Consts.is_dup := !Consts.is_dup + (List.length(synthesized_conjectures) - List.length(filtered_conjectures));
  
  let filtered_valid_conjectures = filter_valid_conjectures filtered_conjectures p_ctxt conjecture
  in let valid_conjectures = List.fold_right (
                                              fun (s, conj, is_valid) acc ->
                                                if is_valid then
                                                (
                                                  (* Hashtbl.replace !cached_lemmas conj.body is_valid; *)
                                                  (s,conj)::acc
                                                )
                                                else 
                                                (
                                                  Hashtbl.replace !cached_lemmas conj.body is_valid;
                                                  acc
                                                )
                                             ) filtered_valid_conjectures []
  in
  Consts.is_false := !Consts.is_false + (List.length(filtered_conjectures) - List.length(valid_conjectures));
  
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
  in let synth_stat = {
                        synthesis_term = (Sexp.string_of_sexpr curr_synth_term);
                        enumerated_exprs = enumerated_exprs;
                        valid_lemmas = filtered_conjectures;
                        original_valid_lemmas = valid_conjectures;
                        provable_lemmas = provable_conjectures;
                        prover_provable_lemmas = prover_provable_conjectures;
                      }
  in synth_stat

let synthesize cached_lemmas p_ctxt ml_examples coq_examples conjecture=
  Log.debug(Consts.fmt "Synthesizing for conjecture %s\n" conjecture.conjecture_str);
  Log.debug(Consts.fmt "#Coq Input Examples %d\n" (List.length coq_examples));
  Log.debug(Consts.fmt "#ML Input Examples %d\n" (List.length ml_examples));
  (
    let first_synth_terms = get_terms_to_synthesize [] conjecture.body_sexp conjecture.lfind_vars conjecture.all_expr_type_table conjecture.body_sexp false
    (* If there are zero synthesis expressions, we add generalized variables to synthesis *)
    in let synth_terms = if List.length first_synth_terms == 0 
                         then get_terms_to_synthesize [] conjecture.body_sexp conjecture.lfind_vars conjecture.all_expr_type_table conjecture.body_sexp true 
                         else first_synth_terms
    in Log.debug (Consts.fmt "Size of synth terms is %d" (List.length synth_terms));
    let sorted_synth_terms = LatticeUtils.sort_by_size synth_terms
    in let synth_count = ref (0) 
    in let synth_stats = List.map (synthesize_lemmas synth_count conjecture ml_examples coq_examples p_ctxt cached_lemmas) sorted_synth_terms
    in let gen_stat = {
                        conjecture = conjecture;
                        is_valid = false;
                        is_provable = false;
                        is_prover_provable = false;
                        synthesis_stats = synth_stats;
                      }
    in Log.write_to_log (genstat_to_string gen_stat) !Log.stats_log_file;
    global_stat := gen_stat :: !global_stat;
    ()
  )

  
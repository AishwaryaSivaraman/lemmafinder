open LatticeUtils
open Consts

type synthesis_stat = {
    synthesis_term : string;
    enumerated_exprs : string list;
    valid_lemmas : (string * conjecture) list;
    original_valid_lemmas : (string * conjecture) list;
    provable_lemmas : (string * conjecture) list;
    prover_provable_lemmas : conjecture list;
}

type generalization_stat = {
    conjecture : conjecture;
    is_valid : bool;
    is_provable : bool;
    is_prover_provable: bool;
    synthesis_stats : synthesis_stat list;
}

let global_stat : generalization_stat list ref = ref []

let get_synthesized_valid_lemmas stats=
    let lemmas = List.fold_left (fun acc g_stat -> 
                            List.append acc
                            (List.fold_left (fun acc s_stat -> 
                                                List.append acc s_stat.valid_lemmas
                                            ) [] g_stat.synthesis_stats
                            )
                   ) [] stats
    in List.fold_left (fun acc (_, c) -> c::acc) [] lemmas

let probable_lemmas_to_string provable_lemmas =
    List.fold_left (fun acc (_, lemma) -> 
                        acc
                        ^
                        fmt "\t\t\t Lemma : %s\n" lemma.conjecture_str
                ) "" provable_lemmas

let lemmas_to_string lemmas =
    List.fold_left (fun acc lemma -> 
                        acc
                        ^
                        fmt "\t\t\t Lemma : %s\n" lemma.conjecture_str
                ) "" lemmas

let get_synthesized_prover_provable_lemmas stats=
    List.fold_left (fun (acc,len) g_stat -> 
                    let new_acc, l = 
                    (List.fold_left
                        (fun (acc_synth,len) s_stat -> 
                            let l = len + (List.length s_stat.prover_provable_lemmas)
                            in List.append s_stat.prover_provable_lemmas acc_synth, l
                        ) (acc, 0) g_stat.synthesis_stats
                    )
                    in new_acc, len + l
                ) ([],0) stats

let get_synthesized_provable_lemmas stats=
   let conj, count =  List.fold_left (fun (acc,len) g_stat -> 
                    let new_acc, l = 
                    (List.fold_left 
                        (fun (acc_synth,len) s_stat -> 
                            let l = len + (List.length s_stat.provable_lemmas)
                            in List.append s_stat.provable_lemmas acc_synth, l
                        ) (acc, 0) g_stat.synthesis_stats
                    )
                    in new_acc, len + l
                ) ([],0) stats
    in let synth_lemmas = List.fold_left (fun acc (_,c) -> c::acc) [] conj
    in synth_lemmas, count

let generalized_lemma_useful stats : conjecture list *int =
    List.fold_left (fun (acc,l) g -> 
                            if g.is_provable then
                            ((g.conjecture::acc), l+1)
                            else (acc,l)
                   ) ([], 0) stats

let generalized_lemma_useful_and_provable stats : conjecture list *int =
    List.fold_left (fun (acc,l) g -> 
                        if g.is_prover_provable then
                        ((g.conjecture::acc), l+1)
                        else (acc,l)
            ) ([], 0) stats

let combine_gen_synth_sort gen_conj synth_conj cache =
    let all_lemmas = List.append gen_conj synth_conj
    in let de_dup_lemmas = List.fold_left (
        fun (acc2) c ->
        if (List.exists (fun s -> String.equal c.body s ) cache) 
        then 
        acc2
        else (c::acc2)
      ) ([]) all_lemmas
    in 
    let sorted_all_lemmas = List.sort (fun a b -> (Sexp.sexp_size (a.body_sexp)) - (Sexp.sexp_size (b.body_sexp))) de_dup_lemmas
    in List.fold_left (
                        fun (acc1,acc2) c ->
                        (acc1 ^ "\n" ^ c.conjecture_str), c.body::acc2
                      ) ("",[]) sorted_all_lemmas
                                

let summarize stats curr_state_lemma =
    (* The last stat is the same as the stuck state, it does not provide any useful indicator *)
    let useful_stats = (List.rev stats)
    in 
    let no_valid_gen_lemmas = List.length (List.filter (fun g -> g.is_valid) (List.tl useful_stats))
    in let gen_useful_provable_lemmas, len_gen_useful_provable_lemmas = generalized_lemma_useful_and_provable (List.tl useful_stats)
    in let gen_provable_lemmas, len_gen_provable_lemmas = generalized_lemma_useful (List.tl useful_stats)
    in let total_synthesized_valid_lemmas = get_synthesized_valid_lemmas (List.tl useful_stats)
    in let str_provable_lemmas, total_synthesized_provable_lemmas = get_synthesized_provable_lemmas (List.tl useful_stats)
    in let str_prover_provable_lemmas, total_synth_prover_provable_lemmas =
    get_synthesized_prover_provable_lemmas (List.tl useful_stats)
    in let cat_1_lemmas_str,cat_1_lemmas = combine_gen_synth_sort gen_useful_provable_lemmas str_prover_provable_lemmas []
    in
    let cat_2_lemmas_str, cat_2_lemmas = combine_gen_synth_sort gen_provable_lemmas str_provable_lemmas cat_1_lemmas
    in 
    let cat3_lemmas_str, cat_3_lemmas = combine_gen_synth_sort [] total_synthesized_valid_lemmas (List.append cat_1_lemmas cat_2_lemmas)
    in let summary =  (fmt "\n### SUMMARY ###\n"
    ^
    fmt "Time to first category 1 (s): %d \n" (!Consts.time_to_category_1)
    ^
    fmt "Total Time: %d \n" (int_of_float(Unix.time ()) - !Consts.start_time)
    ^
    fmt "Total Lemmas: %d \n" !Consts.total_synth
    ^
    fmt "Filter Quickchick: %d \n" !Consts.is_false
    ^
    fmt "Filter duplicate: %d \n" !Consts.is_dup
    ^
    fmt "Filter trivial: %d \n" !Consts.trivial_count
    ^
    fmt "Filter is_version: %d \n" !Consts.is_version_count
    ^
    fmt "Stuck Proof State: %s\n"  (curr_state_lemma)
    ^
    fmt "Yes Cat 1: %b\n" (List.length cat_1_lemmas > 0)
    ^
    fmt "# Generalizations : %d\n" (List.length (List.tl useful_stats))
    ^
    fmt "#Synthesized Lemmas not disprovable : %d\n" (List.length total_synthesized_valid_lemmas)
    ^
    fmt "Provable and Useful in Completing Stuck Goal (Category 1)\n%s\n" cat_1_lemmas_str
    ^
    fmt "Useful in Completing Stuck Goal (Category 2)\n%s\n" cat_2_lemmas_str
    ^
    fmt "Valid Lemmas (Category 3)\n%s\n" cat3_lemmas_str
    )
    in Log.write_to_log summary !Log.stats_summary_file; ()

let valid_lemmas_to_string valid_lemmas =
    List.fold_left (fun acc (synthesized_expr, lemma) -> 
                            acc
                            ^
                            fmt "\t\t\t Myth Term : %s\n" synthesized_expr
                            ^
                            fmt "\t\t\t Lemma : %s\n" lemma.conjecture_str
                   ) "" valid_lemmas

let synthstat_to_string synth_stat =
    fmt "\t\t\n### Synthesis Stats ###\n"
    ^
    fmt "\t\t Synthesis Term : %s\n" synth_stat.synthesis_term
    ^
    fmt "\t\t # Myth Enumerated Terms : %d\n" (List.length synth_stat.enumerated_exprs)
    ^
    fmt "\t\t # Valid Synthesized Lemmas : %d\n" (List.length synth_stat.valid_lemmas)
    ^
    fmt "\t\t Valid Lemmas\n %s\n" (valid_lemmas_to_string synth_stat.valid_lemmas)
    ^
    fmt "\t\t # Lemmas useful to prove original goal : %d\n" (List.length synth_stat.provable_lemmas)
    ^
    fmt "\t\t Lemmas that can prove the original goal \n %s\n" (valid_lemmas_to_string synth_stat.provable_lemmas)
    ^
    fmt "------------------------------------------------------------------------\n"


let synthstats_to_string synthesis_stats =
    List.fold_left (fun acc synth_stat -> acc ^ (synthstat_to_string synth_stat)) "" synthesis_stats

let genstat_to_string gen_stat =
    fmt "\n### Generalization Stat ###\n"
    ^
    fmt "Generalized Conjecture : %s\n" gen_stat.conjecture.conjecture_str
    ^
    fmt "is_valid : %b\n" (gen_stat.is_valid)
    ^ 
    fmt "is_prover_provable (be proven by proverbot): %b\n" (gen_stat.is_prover_provable)
    ^ 
    fmt "is_provable (can help prove original goal): %b\n" (gen_stat.is_provable)
    ^
    fmt "Synthesis Stats : \n %s \n" (synthstats_to_string gen_stat.synthesis_stats)

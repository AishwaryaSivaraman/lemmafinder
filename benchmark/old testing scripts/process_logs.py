import argparse
from genericpath import isdir
import os
import csv
import json
from posixpath import dirname
import subprocess

import coq_serapy
import subprocess
from sexpdata import loads
import multiprocessing
from functools import partial

class LogDetails(object):
    def __init__(self) -> None:
        super().__init__()
        self.log_dir = ""
        self.no_gen_provable = 0 
        self.no_synth_provable = 0
        self.provable_lemmas = []
        self.total_gen = 0
        self.total_synth = 0
        self.is_stuck_provable = False
        self.no_gen_useful_stuck_provable = 0
        self.no_syn_useful_stuck_provable = 0
        self.useful_stuck_provable_lemmas = []
        self.valid_lemmas = []
        self.matches_human = False
        self.is_stronger_than_human = False
        self.is_weaker_than_human = False
        self.matched_lemma = ""
        self.matched_lemma_loc = 0
        self.stronger_lemma = ""
        self.stronger_lemma_loc = 0
        self.weaker_lemma = ""
        self.weaker_lemma_loc = 0
        self.helper_name = "" 
        self.helper_lemma = ""
        self.is_auto_provable = False
        self.top_answer = ""
        self.theorem_prop = ""
        self.helper_prop = ""
        self.top_can_prop = ""
        self.is_success = False
        self.is_in_search_space = False

    def row(self):
        return [self.log_dir,self.is_stuck_provable,self.no_gen_provable,self.no_synth_provable, self.no_gen_useful_stuck_provable,self.no_syn_useful_stuck_provable,len(self.valid_lemmas), self.matches_human, self.matched_lemma,self.matched_lemma_loc,self.stronger_lemma,self.stronger_lemma_loc,self.weaker_lemma, self.weaker_lemma_loc, self.helper_name, self.helper_lemma, self.is_auto_provable, self.top_answer, self.total_synth, self.total_gen, self.theorem_prop, self.helper_prop, self.top_can_prop, self.is_success, self.is_in_search_space]

    def of_string(self, values):
        self.log_dir = values[0]
        self.is_stuck_provable= to_bool(values[1])
        self.no_gen_provable = to_int(values[2])
        self.no_synth_provable = to_int(values[3])
        self.no_gen_useful_stuck_provable = to_int(values[4])
        self.no_syn_useful_stuck_provable = to_int(values[5])
        self.matches_human= to_bool(values[7])
        self.matched_lemma= values[8]
        self.matched_lemma_loc= to_int(values[9])
        self.stronger_lemma= values[10]
        self.stronger_lemma_loc= to_int(values[11])
        self.weaker_lemma= values[12]
        self.weaker_lemma_loc= to_int(values[13])
        self.helper_name= values[14]
        self.helper_lemma= values[15]
        self.is_auto_provable= to_bool(values[16])
        self.top_answer= values[17]
        self.total_synth= to_int(values[18])
        self.total_gen= to_int(values[19])
        self.is_stronger_than_human = self.stronger_lemma_loc==1
        self.is_success = to_bool(values[20])
        if len(values) >= 25:
            self.theorem_prop= values[20]
            self.helper_prop= values[21]
            self.top_can_prop= values[22]
            self.is_success= to_bool(values[23])
            self.is_in_search_space= to_bool(values[24])

    def premise(self, lemma, goal_state):
        proverbot = os.getenv('PROVERBOT')
        premise_file = os.path.join(proverbot, "src/score_premises.py")
        weights_file = os.path.join(proverbot, "data/polyarg-weights.dat")
        process = subprocess.Popen(["python3", premise_file, weights_file, goal_state, lemma], stdout=subprocess.PIPE)
        res = process.communicate()[0].decode("utf-8").split("\n")
        max_score = 0
        for r in res:
            try:
                no = float(r)
            except:
                no = 0
            if no > max_score:
                max_score = no
        return (lemma, max_score)

    def sort_lemmas(self, premise_selection=False, goal_state=""):
        self.provable_lemmas = sorted(self.provable_lemmas, key=compare_lemmas)
        if not premise_selection:
            self.useful_stuck_provable_lemmas = sorted(self.useful_stuck_provable_lemmas, key=compare_lemmas)
            self.valid_lemmas = sorted(self.valid_lemmas, key=compare_lemmas)
        else:
            cat_2_lemmas_with_scores = []
            for l in self.useful_stuck_provable_lemmas:
                cat_2_lemmas_with_scores.append(self.premise(l, goal_state))
            assert len(cat_2_lemmas_with_scores) == len(self.useful_stuck_provable_lemmas)
            self.useful_stuck_provable_lemmas = sorted(cat_2_lemmas_with_scores, key=lambda x: x[1], reverse=True)
            if len(self.useful_stuck_provable_lemmas) > 0:
                self.useful_stuck_provable_lemmas = (list(zip(*self.useful_stuck_provable_lemmas))[0])
            
            cat_3_lemmas_with_scores = []
            for l in self.valid_lemmas:
                cat_3_lemmas_with_scores.append(self.premise(l, goal_state))
            assert len(cat_3_lemmas_with_scores) == len(self.valid_lemmas)
            self.valid_lemmas = sorted(cat_3_lemmas_with_scores, key=lambda x: x[1], reverse=True)
            if len(self.valid_lemmas) > 0:
                self.valid_lemmas = (list(zip(*self.valid_lemmas))[0])

def to_int(value):
    try:
        return int(value)
    except:
        return 0

def to_bool(value):
    if value.upper() == 'FALSE':
        return False
    elif value.upper() == 'TRUE':
        return True
    else: 
        return False

def get_lemmas(benchmark_file):
    import json
    with open(benchmark_file, 'r') as j:
     all_lemmas = json.loads(j.read())    
    return all_lemmas

def parse_arguments():
    parser = argparse.ArgumentParser(
        description=
        "Rank and Generate CSV")
    parser.add_argument('--log_dir', default=None)
    parser.add_argument('--benchmark_file', default=None)
    parser.add_argument('--project', default=False, action="store_true")
    return parser.parse_args(), parser

def write_missing_lemmasto_csv(missing_lemmas, log_dir):
    csv_file = os.path.join(log_dir, "missing.csv")
    column_name = ["Missing", "Reason"]
    with open(csv_file, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(column_name)
        for key, value in missing_lemmas.items():
            writer.writerow([key, value])     

def sort_logs_by_goal_no(log):
    return os.path.basename(log.log_dir).split("_")[4].replace("goal","")

def write_log_objs(csv_file, log_objs):
    column_names = ["log_dir",
"is_stuck_provable",
"no_gen_provable",
"no_synth_provable",
"no_gen_useful_stuck_provable",
"no_syn_useful_stuck_provable",
"len(valid_lemmas)",
"matches_human",
"matched_lemma",
"matched_lemma_loc",
"stronger_lemma",
"stronger_lemma_loc",
"weaker_lemma",
"weaker_lemma_loc",
"helper_name",
"helper_lemm",
"is_provable",
"synth/gen",
"total_synth",
"total_gen",
"stuck_state_prop",
"helper_prop",
"candidate_prop",
"is_success",
"is_in_search_space"
]
    if os.path.exists(csv_file):
        column_names = []
    with open(csv_file, "a", newline="") as f:
        writer = csv.writer(f)
        if len(column_names) > 0:
            writer.writerow(column_names)
        s = sorted(log_objs, key=sort_logs_by_goal_no)
        for log_obj in s:
            writer.writerow(log_obj.row())

class MissingLogException(Exception):
    def __init__(self, message):
        super().__init__(message)

def get_helper_lemma(prelude):
    benchmark_file = os.path.join(prelude, "lemmafinder_bench.txt")
    benchmark_lemmas = get_lemmas(benchmark_file)
    orig_lemma_name = os.path.basename(prelude)
    lemma_filename = ""
    for f in os.listdir(prelude):
         if f.endswith(".txt") and "examples" in f:
             lemma_filename = f.replace(".txt", "").replace("examples_", "")
    
    theorem_name = ""
    alternate_theorem_name = ""
    for k in benchmark_lemmas:
        locs = benchmark_lemmas[k]
        for l in locs:
            if len(theorem_name) > 0:
                continue
            comb_name = l[0].replace("'","") + "_" + str(l[1])+ "_"+l[2]
            split_name = orig_lemma_name.split(lemma_filename + "_")
            if split_name[1] == comb_name:
                theorem_name = l[2].replace("'","")
                alternate_theorem_name = os.path.basename(k).split(".")[0] + "_" + theorem_name
            elif len(split_name) > 2 and split_name[2] == comb_name:
                theorem_name = l[2].replace("'","")
                alternate_theorem_name = os.path.basename(k).split(".")[0] + "_" + theorem_name
            elif len(split_name) > 2 and lemma_filename + "_" + split_name[2] == comb_name:
                theorem_name = lemma_filename + '_' + split_name[2].split('_', 1)[1]
            elif len(split_name) > 3:
                theorem_name = lemma_filename + '_' + split_name[3]
    return theorem_name, alternate_theorem_name

def is_proof_complete(prelude, imports, proof_cmds, stmts=[]):
    with coq_serapy.SerapiContext(
            ["sertop", "--implicit"],    
            None,
            prelude) as coq:
        for imp in imports:
            coq.run_stmt(imp)
        for stmt in stmts:
            coq.run_stmt(stmt)
        try:
            cmds_left, cmds_run = coq.run_into_next_proof(
            proof_cmds)
            _, _ = coq.finish_proof(cmds_left)
            return True
        except coq_serapy.CoqExn:
            return False 
        except:
            return False

def get_prop(prelude, imports, lemma):
    if lemma == "":
        return "", False
    lemma = lemma.strip()
    if lemma[len(lemma)-1] != ".":
        lemma = lemma + "."
    with coq_serapy.SerapiContext(
            ["sertop", "--implicit"],    
            None,
            prelude) as coq:
        for imp in imports:
            coq.run_stmt(imp)
        try:
            coq.run_stmt(lemma)
            coq.run_stmt("Proof.")
            coq.run_stmt("intros.")
            goal_from_lemma = "(" + coq.proof_context.fg_goals[0].goal + ")"
            prop = loads(goal_from_lemma)[0].value()
        except:
            prop = ""
        is_conditional = "->" in lemma
        return prop, is_conditional
        
            
def is_stronger_than_human(human_lemma_name, human_lemma, synth_lemma, prelude, imports):
    synth_lemma_name = synth_lemma.split(":")[0].replace("Lemma ", "").strip()
    if synth_lemma[len(synth_lemma)-1] == ".":
        stmts = [synth_lemma, "Admitted."]
    else:
        stmts = [synth_lemma+".", "Admitted."]
    apply_auto_proof_cmds = [human_lemma.replace(human_lemma_name, "humanlemma"), "Proof.",
        "intros.",
        f"apply {synth_lemma_name}.",
        "auto.",
        "Qed."]
    is_proof_complete_apply_auto = is_proof_complete(prelude, imports, apply_auto_proof_cmds, stmts)
    apply_proof_cmds = [human_lemma.replace(human_lemma_name, "humanlemma"), "Proof.",
        "intros.",
        f"apply {synth_lemma_name}.",
        "Qed."]
    is_proof_complete_apply = is_proof_complete(prelude, imports, apply_proof_cmds, stmts)
    rewrite_proof_cmds = [human_lemma.replace(human_lemma_name, "humanlemma"), "Proof.",
        "intros.",
        f"rewrite -> {synth_lemma_name}.",
        "reflexivity.",
        "Qed."]
    is_proof_complete_rewrite = is_proof_complete(prelude, imports, rewrite_proof_cmds, stmts)
    rewrite_proof_cmds = [human_lemma.replace(human_lemma_name, "humanlemma"), "Proof.",
        "intros.",
        f"rewrite <- {synth_lemma_name}.",
        "reflexivity.",
        "Qed."]
    is_proof_complete_rewrite_left = is_proof_complete(prelude, imports, rewrite_proof_cmds, stmts)
    return is_proof_complete_apply or is_proof_complete_rewrite or is_proof_complete_rewrite_left or is_proof_complete_apply_auto

def is_weaker_than_human(human_lemma_name, synth_lemma, prelude, imports):
    if synth_lemma[len(synth_lemma)-1] == ".":
        name =  synth_lemma 
    else:
        name =  synth_lemma+"."
    apply_auto_proof_cmds = [name, "Proof.",
        "intros.",
        f"apply {human_lemma_name}.",
        "auto.",
        "Qed."]
    is_proof_complete_apply_auto = is_proof_complete(prelude, imports, apply_auto_proof_cmds)
    apply_proof_cmds = [name, "Proof.",
        "intros.",
        f"apply {human_lemma_name}.",
        "Qed."]
    is_proof_complete_apply = is_proof_complete(prelude, imports, apply_proof_cmds)
    rewrite_proof_cmds = [name, "Proof.",
        "intros.",
        f"rewrite -> {human_lemma_name}.",
        "reflexivity.",
        "Qed."]
    is_proof_complete_rewrite = is_proof_complete(prelude, imports, rewrite_proof_cmds)
    rewrite_proof_cmds = [name, "Proof.",
        "intros.",
        f"rewrite <- {human_lemma_name}.",
        "reflexivity.",
        "Qed."]
    is_proof_complete_rewrite_left = is_proof_complete(prelude, imports, rewrite_proof_cmds)
    return is_proof_complete_apply or is_proof_complete_rewrite or is_proof_complete_rewrite_left or is_proof_complete_apply_auto

def get_goal_state(fname):
    file = open(fname, 'r')
    lines = file.readlines()
    state = ""
    is_state = False
    i = 0
    for i in range(0, len(lines)):
        if "Lemma lfind_state" in lines[i]:
            state += lines[i]
            i+=1
            while "Admitted" not in lines[i]:
                state+=lines[i]
                i+=1
        if i >= len(lines):
            break
    return state

def get_imports(fname):
    file = open(fname, 'r')
    lines = file.readlines()
    imports  = []
    for l in lines:
        if "Require Import" in l and "LFind" not in l:
            imports.append(l.strip())
    return imports

def getSizeOfNestedList(listOfElem):
    count = 0
    for elem in listOfElem:
        if type(elem) == list:  
            count += getSizeOfNestedList(elem)
        else:
            count += 1
    return count

def compare_lemmas(lemma):
    lemma_body = lemma.split(",",1)[1].strip().replace('\'', '')
    sexp_lemma = []
    try:
        sexp_lemma = loads(lemma_body)
    except:
        sexp_lemma = loads ("(" + lemma_body + ")")
    return getSizeOfNestedList(sexp_lemma)

def get_stuck_provable(log_file):
    contents = open(log_file).readlines()
    is_stuck_provable = False
    gen_stat_count = 0
    for c in contents:
        if "### Generalization Stat ###" in c:
            gen_stat_count += 1
        if gen_stat_count == 1 and "is_prover_provable" in c:
            return (c.split(":")[1].strip()=="true")
    return is_stuck_provable

def get_cat_2_from_log(log_file):
    contents = open(log_file).readlines()
    is_cat_2 = False
    cat_2 = []
    for l in contents:
        if "# Lemmas useful to prove original goal" in l:
            is_cat_2 = True
        if "Lemma :" in l and is_cat_2:
            cat_2.append(l.replace("Lemma :", "Lemma").strip())
        if "### Synthesis Stats ###" in l:
            is_cat_2 = False
    return cat_2

def get_runtimes(lemma_file):
    contents = open(lemma_file).readlines()
    time_to_first = 0
    total_time = 0
    for l in contents:
        if "Time to first category" in l and ":" in l:
            time_to_first = float(l.split(":")[1].strip())
        elif "Total Time" in l and ":" in l:
            total_time = float(l.split(":")[1].strip())
            if time_to_first == 0:
                time_to_first = total_time
    return time_to_first, total_time
            
def get_filter_data(lemma_file):
    contents = open(lemma_file).readlines()
    total_lemma = 0
    after_qc = 0
    trivial = 0
    duplicate = 0
    version = 0
    after_other_filters = 0
    for l in contents:
        if "Total Lemmas:" in l:
            total_lemma = int(l.split(":")[1].strip())
        if "Filter Quickchick:" in l:
            no_qc = int(l.split(":")[1].strip())
            after_qc = total_lemma - no_qc
        if "Filter duplicate:" in l:
            duplicate = int(l.split(":")[1].strip())
        if "Filter trivial:" in l:
            trivial = int(l.split(":")[1].strip())
        if "Filter is_version:" in l:
            version = int(l.split(":")[1].strip())
            after_other_filters = total_lemma - (duplicate + trivial + version+no_qc)
    return total_lemma, after_qc, after_other_filters

def get_ranked_lemmmas(lemma_file):
    contents = open(lemma_file).readlines()
    log_obj = LogDetails()
    is_provable = False
    is_useful = False
    is_valid = False
    for l in contents:
        if ':' in l and '#' in l:
            val = int(l.split(":")[1])
        if "# Generalizations :" in l:
            log_obj.total_gen = val
        if "#Synthesized Lemmas not disprovable :" in l:
            log_obj.total_synth = val
        if "Provable and Useful in Completing Stuck Goal (Category 1)" == l.strip():
            is_provable = True
        if "conj" in l and ":" in l and is_provable:
            lem = "Lemma " + l
            log_obj.provable_lemmas.append(lem)
        if "Useful in Completing Stuck Goal (Category 2)" == l.strip():
            is_provable = False
            is_useful = True
        if "conj" in l and ":" in l and is_useful:
            lem = "Lemma " + l
            log_obj.useful_stuck_provable_lemmas.append(lem.strip())
        if "Valid Lemmas (Category 3)" == l.strip():
            is_valid = True
            is_useful = False
            is_provable = False
        if "conj" in l and ":" in l and is_valid:
            lem = "Lemma " + l
            log_obj.valid_lemmas.append(lem)
    return log_obj

def get_lemmas_from_file(filename):
    contents = open(filename).readlines()
    is_auto_provable = False
    is_cat_2 = False
    is_valid = False
    log_obj = LogDetails()
    for l in contents:
        if "Provable and Useful in Completing Stuck Goal" == l.strip():
            is_auto_provable = True
        elif is_auto_provable and "conj" in l:
            log_obj.provable_lemmas.append(l)
        elif "Useful in Completing Stuck Goal" == l.strip():
            is_auto_provable = False
            is_cat_2 = True
        elif is_cat_2 and "conj" in l:
            log_obj.useful_stuck_provable_lemmas.append(l)
        elif "Valid Lemmas" == l.strip():
            is_auto_provable = False
            is_cat_2 = False
            is_valid = True
        elif is_valid and "conj" in l:
            log_obj.valid_lemmas.append(l)
    return log_obj

def  sort_and_print_lemmas(log_dir, log_obj):
    f_name = os.path.basename(log_obj.log_dir).replace("_lfind_","")
    l_file = os.path.join(log_dir, f_name)
    f = open(l_file, "w")
    f.write("Provable and Useful in Completing Stuck Goal\n")
    s = log_obj.provable_lemmas
    # sorted(log_obj.provable_lemmas, key=compare_lemmas)
    f.writelines('\n'.join(s))
    f.write("\nUseful in Completing Stuck Goal\n")
    s = log_obj.useful_stuck_provable_lemmas
    # sorted(log_obj.useful_stuck_provable_lemmas, key=compare_lemmas)
    f.writelines('\n\n'.join(s))
    f.write("\nValid Lemmas\n")
    s = log_obj.valid_lemmas
    # sorted(log_obj.valid_lemmas, key=compare_lemmas) 
    f.writelines('\n'.join(s))
    f.close()
    
def process_lemma(helper_lemma_name,helper_lemma,f_name,imports,l):
    try:
        isweaker = is_weaker_than_human(helper_lemma_name, l, f_name, imports)
        isstronger = is_stronger_than_human(helper_lemma_name, helper_lemma, l, f_name, imports)
        return isweaker, isstronger
    except:
        return False, False

def get_lemma_from_all_lemmas(all_lemmas, lemma_name):
    lemma = ""
    for key, value in all_lemmas.items():
        if lemma_name == key:
            lemma = value
    return lemma

def get_locations(benchmark_file):
    with open(benchmark_file, 'r') as j:
     lemma_dict = json.loads(j.read())    
    return lemma_dict

def get_lfind_lemma(lfind_state_file):
    file = open(lfind_state_file, 'r')
    lines = file.readlines()
    for l in lines:
        if "Lemma" in l:
            return l    

def read_logs_from_folder(log_dir):
    total_times = []
    time_to_firsts = []
    total_lemmas_all = []
    total_afterquickchick = []
    total_after_other_filters = []
    for root, dirs, files in os.walk(log_dir):
        for name in dirs:
            f_name = os.path.join(root, name)
            if os.path.isdir(f_name) and "_lfind_" in f_name:
                l_file = os.path.join(f_name, "lfind_summary_log.txt")
                if os.path.exists(l_file):
                    time_to_first, total_time = get_runtimes(l_file)
                    if time_to_first < total_time:
                        time_to_firsts.append(time_to_first/60.0)
                        total_times.append(time_to_first/60.0)
                    else:
                        total_times.append(total_time/60.0)
                    total_lemma, after_qc, after_others = get_filter_data(l_file)
                    total_lemmas_all.append(total_lemma)
                    total_afterquickchick.append(after_qc)
                    total_after_other_filters.append(after_others)
        break
    return total_times, time_to_firsts, total_lemmas_all, total_afterquickchick,total_after_other_filters

def run_process_logs(log_dir, helper_lemma_locations, is_project, source_folder=""):
    op_csv = os.path.join(log_dir, "lfind_benchmark_summary.csv")
    count_total_lfind_logs = 0
    total_lemmas = 0
    missing_lemmas = 0
    missing_lemmas_profile = {}
    provable_by_proverbot = 0
    stuck_state_provable = 0
    log_objs = []
    useful_stuck_provable_lemmas = 0
    matches_human = 0
    stronger_than_human = 0
    weaker_than_human = 0
    total_times = []
    time_to_firsts = []
    total_lemmas_all = []
    total_afterquickchick = []
    total_after_other_filters = []
    for file in helper_lemma_locations:
        for location in helper_lemma_locations[file]:
            file = os.path.join(source_folder, file)
            file_name = os.path.basename(file)
            source_folder = dirname(file)
            helper_prefix = os.path.splitext(file_name)[0]
            lemma_name = location[2].replace("'","")

            destination_folder = os.path.join(os.path.dirname(source_folder),str(os.path.basename(source_folder))+"_lf_" + os.path.splitext(file_name)[0] + "_" + location[0].replace("'","") + "_" + str(location[1])+ "_"+lemma_name)

            stuck_folder = os.path.join(os.path.dirname(source_folder),"_lfind_" + str(os.path.basename(source_folder))+"_lf_" + os.path.splitext(file_name)[0] + "_" + location[0].replace("'","") + "_" + str(location[1])+"_" + lemma_name)

            if is_project:
                helper_lemma_name = lemma_name
            else:
                helper_lemma_name = helper_prefix + "_" + lemma_name

            f_name_log = os.path.basename(stuck_folder).replace("_lfind_","")
            l_log_file = os.path.join(log_dir, f_name_log)
            if os.path.isfile(l_log_file):
                # if the log has been processed skip it
                print(l_log_file)
                continue

            if isdir(destination_folder) and isdir(stuck_folder):
                # carry out log analysis
                benchmark_file = os.path.join(source_folder, "lemmafinder_all_lemmas.txt")
                print(benchmark_file)
                all_lemmas = get_lemmas(benchmark_file)
                l_file = os.path.join(stuck_folder, "lfind_summary_log.txt")
                log_file = os.path.join(stuck_folder, "lfind_log.txt")
                count_total_lfind_logs +=1
                log_obj = None

                if os.path.isfile(l_file) :
                    # we need to remove trivial ones
                    lfind_state = os.path.join(stuck_folder, "lfind_state.v")
                    helper_lemma = get_lemma_from_all_lemmas(all_lemmas, helper_lemma_name)
                    helper_lemma_name = lemma_name
                    if helper_lemma == "":
                        print("helper lemma not found")
                        # import sys
                        # sys.exit(0)
                    imports = get_imports(lfind_state)
                    lfind_state_lemma = get_lfind_lemma(lfind_state)
                    lfind_state_prop, _ = get_prop(destination_folder, imports, lfind_state_lemma)
                    helper_lemma_prop, helper_is_conditional = get_prop(destination_folder, imports, helper_lemma)
                    log_obj = get_ranked_lemmmas(l_file)
                    time_to_first, total_time = get_runtimes(l_file)
                    total_lemma, after_qc, after_others = get_filter_data(l_file)
                    total_lemmas_all.append(total_lemma)
                    total_afterquickchick.append(after_qc)
                    total_after_other_filters.append(after_others)
                    cat_2_lemmas_from_log = get_cat_2_from_log(log_file)
                    if len(cat_2_lemmas_from_log) > len(log_obj.useful_stuck_provable_lemmas):
                        for l in cat_2_lemmas_from_log:
                            if l not in log_obj.useful_stuck_provable_lemmas:
                                log_obj.useful_stuck_provable_lemmas.append(l)
                    goal_state = get_goal_state(lfind_state).strip()
                    log_obj.sort_lemmas(False, goal_state)
                    lemma_synth = []
                    lemma_synth.extend(log_obj.provable_lemmas)
                    lemma_synth.extend(log_obj.useful_stuck_provable_lemmas)
                    lemma_synth.extend(log_obj.valid_lemmas)
                    log_obj.is_stuck_provable = get_stuck_provable(log_file)      
                    log_obj.helper_name = helper_lemma_name 
                    log_obj.helper_lemma = helper_lemma
                    pool_obj = multiprocessing.Pool(multiprocessing.cpu_count())
                    func_process = partial(process_lemma, helper_lemma_name,helper_lemma,destination_folder,imports)
                    processed_lemmas = pool_obj.map(func_process, lemma_synth)
                    for i in range(0, len(processed_lemmas)):
                        isweaker = processed_lemmas[i][0]
                        isstronger = processed_lemmas[i][1]
                        l = lemma_synth[i]

                        if isweaker and isstronger and (not log_obj.matches_human):
                            print(f"similar to user provided lemma {helper_lemma} : {l}")
                            log_obj.matches_human = True
                            log_obj.matched_lemma_loc = i + 1
                            log_obj.matched_lemma = l
                            if "synth" in l:
                                log_obj.top_answer = "S"
                            else:
                                log_obj.top_answer = "G"
                        elif isstronger and (not log_obj.is_stronger_than_human):
                            print(f"stronger than lemma {helper_lemma} : {l}")
                            log_obj.is_stronger_than_human = True
                            log_obj.stronger_lemma = l
                            log_obj.stronger_lemma_loc = i + 1
                            if "synth" in l:
                                log_obj.top_answer = "S"
                            else:
                                log_obj.top_answer = "G"
                        elif isweaker and (not log_obj.is_weaker_than_human):
                            print(f"weaker than lemma {helper_lemma} : {l}")
                            log_obj.is_weaker_than_human = True
                            log_obj.weaker_lemma = l
                            log_obj.weaker_lemma_loc = i + 1
                            if "synth" in l:
                                log_obj.top_answer = "S"
                            else:
                                log_obj.top_answer = "G"
                    log_obj.log_dir = stuck_folder
                    log_obj.is_auto_provable = len(log_obj.provable_lemmas) > 0
                    if log_obj.is_auto_provable:
                            time_to_firsts.append(time_to_first/60.0)
                            total_times.append(time_to_first/60.0)
                    else:
                        total_times.append(total_time/60.0)
                    top_lemma = ""
                    if log_obj.is_auto_provable:
                        log_obj.is_in_search_space = True
                        log_obj.is_success = True
                        top_lemma = log_obj.provable_lemmas[0]
                    elif log_obj.matches_human:
                        if log_obj.matched_lemma_loc < 10 and log_obj.matched_lemma_loc >= 0:
                            log_obj.is_success = True
                            log_obj.is_in_search_space = True
                        else:
                            log_obj.is_in_search_space = True
                        top_lemma = log_obj.matched_lemma
                    elif log_obj.is_stronger_than_human:
                        if log_obj.stronger_lemma_loc < 10 and log_obj.stronger_lemma_loc >=0:
                            log_obj.is_success = True
                            log_obj.is_in_search_space = True
                        else:
                            log_obj.is_in_search_space = True
                        top_lemma = log_obj.stronger_lemma
                    top_lemma_prop, top_lemma_is_conditional = get_prop(destination_folder, imports, top_lemma)

                    log_obj.theorem_prop = lfind_state_prop
                    if helper_is_conditional:
                        log_obj.helper_prop = "cond"
                    else:
                        log_obj.helper_prop = helper_lemma_prop
                    if top_lemma_is_conditional:
                        log_obj.top_can_prop = "cond"
                    else:
                        log_obj.top_can_prop = top_lemma_prop

                    if log_obj.is_auto_provable:
                        if "synth" in log_obj.provable_lemmas[0]:
                            log_obj.top_answer = "S"
                        else:
                            log_obj.top_answer = "G"
                    sort_and_print_lemmas(log_dir, log_obj)
                if log_obj:
                    log_objs.append(log_obj)
                    write_log_objs(os.path.join(log_dir,"summary.csv"), [log_obj])
                    provable_by_proverbot += int((log_obj.no_gen_provable + log_obj.no_synth_provable) > 0)
                    stuck_state_provable += int(log_obj.is_stuck_provable)
                    useful_stuck_provable_lemmas+=(len(log_obj.useful_stuck_provable_lemmas) > 0)
                else:
                    total_lemmas +=1
                    missing_lemmas_profile[stuck_folder] = "Either lfind or the original folder didnt get created!"
    write_missing_lemmasto_csv(missing_lemmas_profile, log_dir)
    # write_log_objs(os.path.join(log_dir,"summary.csv"), log_objs)
    matches_human = 0
    stronger_than_human = 0
    weaker_than_human = 0
    for o in log_objs:
        matches_human +=o.matches_human
        stronger_than_human +=o.is_stronger_than_human
        weaker_than_human += o.is_weaker_than_human
    return log_objs, total_times, time_to_firsts, total_lemmas_all, total_afterquickchick, total_after_other_filters


def main():
    args, parser = parse_arguments()
    helper_lemma_dict = get_locations(args.benchmark_file)
    log_objs, total_times, time_to_firsts = run_process_logs(args.log_dir, helper_lemma_dict, args.project)

if __name__ == "__main__":
    main()
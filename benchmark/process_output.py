import argparse
from cmath import log
import os
import csv
from posixpath import dirname, split
from re import S, search, sub
import sys

from torch import log_
import coq_serapy
import subprocess
import shutil
import operator, functools
from sexpdata import loads, dumps
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

    def row(self):
        return [self.log_dir,self.is_stuck_provable,self.no_gen_provable,self.no_synth_provable, self.no_gen_useful_stuck_provable,self.no_syn_useful_stuck_provable,len(self.valid_lemmas), self.matches_human, self.matched_lemma,self.matched_lemma_loc,self.stronger_lemma,self.stronger_lemma_loc,self.weaker_lemma, self.weaker_lemma_loc, self.helper_name, self.helper_lemma, self.is_auto_provable, self.top_answer, self.total_synth, self.total_gen]
    
    def sort_lemmas(self):
        self.provable_lemmas = sorted(self.provable_lemmas, key=compare_lemmas)
        self.useful_stuck_provable_lemmas = sorted(self.useful_stuck_provable_lemmas, key=compare_lemmas)
        self.valid_lemmas = sorted(self.valid_lemmas, key=compare_lemmas)

def get_lemmas(benchmark_file):
    import json
    with open(benchmark_file, 'r') as j:
     all_lemmas = json.loads(j.read())    
    return all_lemmas

def parse_arguments():
    parser = argparse.ArgumentParser(
        description=
        "Rank and Generate CSV")
    parser.add_argument('--lfind_op', default=None)
    parser.add_argument('--log_dir', default=None)
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
"total_gen"]
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
         if f.endswith("_wsynth.ml"):
             lemma_filename = f.replace("_wsynth.ml", "")
    if lemma_filename == "":
        lemma_filename = orig_lemma_name.split("_lf_")[1]
        lemma_filename = lemma_filename.split("_")[0]
    theorem_name = ""
    alternate_theorem_name = ""
    for k in benchmark_lemmas:
        locs = benchmark_lemmas[k]
        for l in locs:
            comb_name = l[0].replace("'","") + "_" + str(l[1])+ "_"+l[2]
            split_name = orig_lemma_name.split(lemma_filename + "_")
            if split_name[1] == comb_name:
                theorem_name = l[2].replace("'","")
                alternate_theorem_name = os.path.basename(k).split(".")[0] + "_" + theorem_name
            elif len(split_name) > 2 and split_name[2] == comb_name:
                theorem_name = l[2].replace("'","")
                alternate_theorem_name = os.path.basename(k).split(".")[0] + "_" + theorem_name
    return theorem_name, alternate_theorem_name

def is_proof_complete(prelude, imports, proof_cmds, stmts=[]):
    print(proof_cmds)
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

def is_stronger_than_human(human_lemma_name, human_lemma, synth_lemma, prelude, imports):
    synth_lemma_name = synth_lemma.split(":")[0].replace("Lemma ", "").strip()
    if synth_lemma[len(synth_lemma)-1] == ".":
        stmts = [synth_lemma, "Admitted."]
    else:
        stmts = [synth_lemma+".", "Admitted."]
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
    return is_proof_complete_apply or is_proof_complete_rewrite or is_proof_complete_rewrite_left

def is_weaker_than_human(human_lemma_name, synth_lemma, prelude, imports):
    if synth_lemma[len(synth_lemma)-1] == ".":
        name =  synth_lemma 
    else:
        name =  synth_lemma+"."
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
    return is_proof_complete_apply or is_proof_complete_rewrite or is_proof_complete_rewrite_left

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
    lemma_body = lemma.split(",")[1].strip()
    sexp_lemma = loads(lemma_body)
    # return len(lemma.split(",")[1])
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
            log_obj.useful_stuck_provable_lemmas.append(lem)
        if "Valid Lemmas (Category 3)" == l.strip():
            is_valid = True
            is_useful = False
            is_provable = False
        if "conj" in l and ":" in l and is_valid:
            lem = "Lemma " + l
            log_obj.valid_lemmas.append(lem)
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
    f.writelines('\n'.join(s))
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

def run(lfind_op, log_dir):
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
    for root, dirs, files in os.walk(lfind_op):
        for name in dirs:
            f_name = os.path.join(root, name)
            
            if os.path.isdir(f_name) and "_lfind_" in f_name:
                benchmark_file = os.path.join(os.path.dirname(f_name),f_name.split("_lfind_")[1].split("_lf_")[0], "lemmafinder_all_lemmas.txt")
                all_lemmas = get_lemmas(benchmark_file)
                lf_name = os.path.basename(f_name).replace("_lfind_","")
                # l_file = os.path.join(log_dir, lf_name)
                l_file = os.path.join(f_name, "lfind_summary_log.txt")
                log_file = os.path.join(f_name, "lfind_log.txt")
                count_total_lfind_logs +=1
                log_obj = None
                f_name_log = os.path.basename(f_name).replace("_lfind_","")
                l_log_file = os.path.join(log_dir, f_name_log)
                if os.path.isfile(l_log_file):
                    print(l_log_file)
                    continue

                if os.path.isfile(l_file) :
                    # we need to remove trivial ones
                    lfind_state = os.path.join(f_name, "lfind_state.v")
                    helper_lemma_name, alternate_helper_lemma_name = get_helper_lemma(f_name)
                    try:
                        helper_lemma = all_lemmas[helper_lemma_name]
                        # continue
                    except:
                        try:
                            helper_lemma = all_lemmas[alternate_helper_lemma_name]
                        except:
                            helper_lemma = ""
                            print(f"helper was not found {helper_lemma_name}")
                            print(f_name)
                            print(benchmark_file)
                    imports = get_imports(lfind_state)
                    log_obj = get_ranked_lemmmas(l_file)
                    log_obj.sort_lemmas()
                    lemma_synth = []
                    lemma_synth.extend(log_obj.provable_lemmas)
                    lemma_synth.extend(log_obj.useful_stuck_provable_lemmas)
                    lemma_synth.extend(log_obj.valid_lemmas)

                    print(len(lemma_synth))       
                    log_obj.is_stuck_provable = get_stuck_provable(log_file)      
                    log_obj.helper_name = helper_lemma_name 
                    log_obj.helper_lemma = helper_lemma
                    pool_obj = multiprocessing.Pool(multiprocessing.cpu_count()-1)
                    func_process = partial(process_lemma, helper_lemma_name,helper_lemma,f_name,imports)
                    processed_lemmas = pool_obj.map(func_process, lemma_synth)
                    for i in range(0, len(processed_lemmas)):
                        isweaker = processed_lemmas[i][0]
                        isstronger = processed_lemmas[i][1]
                        l = lemma_synth[i]
                    # for i in range(0, len(lemma_synth)):
                        # l = lemma_synth[i]
                        # print(f"helper lemma is {helper_lemma}")
                        # print(f"helper lemma is {helper_lemma_name}")
                        # if helper_lemma == "":
                        #     break
                        # isweaker = is_weaker_than_human(helper_lemma_name, l, f_name, imports)
                        # isstronger = is_stronger_than_human(helper_lemma_name, helper_lemma, l, f_name, imports)
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
                    log_obj.log_dir = f_name
                    log_obj.is_auto_provable = len(log_obj.provable_lemmas) > 0
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
            if os.path.isdir(f_name) and "_lfind_" not in f_name and "_lf_" in f_name:
                total_lemmas +=1
                log_name = f"_lfind_{name}"
                if not os.path.isdir(os.path.join(root, log_name)):
                    missing_lemmas_profile[f_name] = "_lfind_ was not generated"
        break
    write_missing_lemmasto_csv(missing_lemmas_profile, log_dir)
    # write_log_objs(os.path.join(log_dir,"summary.csv"), log_objs)
    matches_human = 0
    stronger_than_human = 0
    weaker_than_human = 0
    for o in log_objs:
        matches_human +=o.matches_human
        stronger_than_human +=o.is_stronger_than_human
        weaker_than_human += o.is_weaker_than_human

    print(f"#Lemmas matching humans/#Lemmas: {matches_human}/{total_lemmas-(len(missing_lemmas_profile))}")
    print(f"#Lemmas stronger than humans/#Lemmas: {stronger_than_human}/{total_lemmas-(len(missing_lemmas_profile))}")
    print(f"#Lemmas weaker than humans/#Lemmas: {weaker_than_human}/{total_lemmas-(len(missing_lemmas_profile))}")
    return provable_by_proverbot, total_lemmas, (len(missing_lemmas_profile)), stuck_state_provable, useful_stuck_provable_lemmas


def main():
    args, parser = parse_arguments()
    provable_by_proverbot, total_lemmas, missing_lemmas,stuck_state_provable,useful_stuck_provable_lemmas = run(args.lfind_op, args.log_dir)
    print(f"#Lemmas stuck state provable/#Lemmas: {stuck_state_provable}/{total_lemmas-missing_lemmas}")
    print(f"#Lemmas that are fully provable/#Lemmas: {provable_by_proverbot}/{total_lemmas-missing_lemmas}")
    print(f"#Lemmas that help prove/#Lemmas: {useful_stuck_provable_lemmas}/{total_lemmas-missing_lemmas}")
    print(f"#Lemmas that are missing/#Lemmas: {missing_lemmas}/{total_lemmas}")

if __name__ == "__main__":
    main()

#!/usr/bin/env python3

import argparse
from ast import arg
import os
import json
import re

from typing import Tuple

def parse_arguments() -> Tuple[argparse.Namespace, argparse.ArgumentParser]:
    parser = argparse.ArgumentParser(
        description=
        "Count the number of proofs that uses helper lemma")
    parser.add_argument('--prelude', default=".")
    parser.add_argument('--output', default=None)
    parser.add_argument('--project', default=False, action="store_true")
    return parser.parse_args(), parser

def isProofStatement(line):
    line = line.strip()
    if re.search("^Theorem.*\:",line) is not None:
        return True
    if re.search("^Lemma.*\:",line) is not None:
        return True
    if re.search("^Corollary.*\:",line) is not None:
        return True
    return False

def get_all_lemmas(folder, is_project):
    lemmas = {}
    lemma_name_content = {}
    no_lemmas = 0
    lemma_name = ""
    lemma_content = ""
    file_lemmas_dict = {}
    for directory, subdirectories, files in os.walk(folder):
        for file in files:
            if file.endswith(".v"):
                try:
                    with open(os.path.join(directory, file)) as f:
                        for line in f:
                            if isProofStatement(line):
                                if is_project:
                                    file_lemma_name = line.split()[1].replace(":","")
                                else:
                                    file_lemma_name = file.split(".")[0] + "_"+line.split()[1].replace(":","")
                                lemma_name = line.split()[1].replace(":","")
                                lemma_content = line
                            elif ("Proof" in line or "Admitted" in line) and (len(lemma_name) > 0):
                                lemmas[lemma_name] = 1
                                lemma_name_content[file_lemma_name] = lemma_content.replace("\n","")
                                no_lemmas +=1
                                lemma_name = ""
                                lemma_content = ""
                            else:
                                lemma_content = lemma_content + line
                except Exception as e:
                    print(e)
                    print (f"Error processing {directory}/{file}")
    return lemmas, no_lemmas, lemma_name_content


def tactic_stats(file, tactics_after_rewrite, lemma_names):
    with open(file) as f:
        for line in f:
            content = line.split(".")
            for i in range(0, len(content)):
                if "rewrite" in content[i] or "apply" in content[i]:
                    c = content[i].split()
                    helper_name = c[len(c)-1].replace(";","")
                    helper_name = helper_name.replace("(","")
                    if helper_name in lemma_names:
                        if i+1 < len(content):
                            t=[]
                            if "Bool" in content[i]:
                                if i+2 < len(content):
                                    t = content[i+2].split()
                            else:
                                t = content[i+1].split()
                            if len(t) > 0:
                                tactic = t[0]
                                if "rewrite" in tactic:
                                    print(content)
                                if tactic in tactics_after_rewrite.keys():
                                    tactics_after_rewrite[tactic] +=1
                                else:
                                    tactics_after_rewrite[tactic] = 1

def count_file(file, lemma_names, lemma_files_names, lemmas_so_far):
    count_helper = 0
    lemma_name = ""
    line_number = -1
    try:
        with open(file) as f:
            start_proof = False
            for line in f:
                line_number+=1
                if start_proof:
                    content = line.split()
                    index = 0
                    helper_indices = []
                    for c in content:
                        if "rewrite"==c or "apply"==c:
                            # if len(content) > index + 2 and content[index+2] != "with":
                            if len(content) > index + 1 and (content[index+1].replace('.','')) in lemma_names:
                                helper_indices.append((index+1,content[index+1].replace('.','')))
                            elif len(content) > index + 2 and (content[index+2].replace('.','')) in lemma_names:
                                helper_indices.append((index+2, content[index+2].replace('.','')))
                            elif len(content) > index + 1 and (content[index+1].replace(';','')) in lemma_names:
                                helper_indices.append((index+1,content[index+1].replace(';','')))
                            elif len(content) > index + 2 and (content[index+2].replace(';','')) in lemma_names:
                                helper_indices.append((index+2, content[index+2].replace(';','')))
                            elif len(content) > index + 2 and (content[index+2].replace('(','')) in lemma_names:
                                helper_indices.append((index+2,content[index+2].replace('(','')))
                            elif len(content) > index + 1 and (content[index+1].replace('(','')) in lemma_names:
                                helper_indices.append((index+1,content[index+1].replace('(','')))
                        index+=1
                    
                    helper_indices_len = 0
                    while helper_indices_len < len(helper_indices):
                        if file not in lemma_files_names:
                            file_name = os.path.basename(file)
                            lemma_files_names[file_name] = []
                        lemma_files_names[file_name].append((lemma_name,line_number,helper_indices[helper_indices_len][1]))
                        count_helper+=1
                        helper_indices_len += 1                   
                        # start_proof = False
                if isProofStatement(line):
                    lemma_name = line.split()[1].replace(":","")
                if "Proof" in line:
                    start_proof = True
                if "Qed" in line or "Admitted" in line:
                    start_proof = False
    except Exception as e:
        print(e)
        print (f"Error processing {file}")
    return count_helper

def count(folder, output_folder, is_project):
    no_coq_files = 0
    no_with_helper = 0
    lemmas, no_lemmas, lemma_content = get_all_lemmas(folder, is_project)
    write_lemmas(lemma_content, output_folder)
    lemma_files_names = {}
    lemmas_so_far = {}
    tactics_dict = {}
    for directory, dirs, files in os.walk(folder):
        for file in files:
            if file.endswith(".v"):
                no_coq_files += 1
                no_with_helper += count_file(os.path.join(directory, file), lemmas, lemma_files_names, lemmas_so_far)
                tactic_stats(os.path.join(directory, file), tactics_dict, lemmas)
    return no_coq_files,no_with_helper,no_lemmas, lemma_files_names, tactics_dict

def write_lemmas(content, output_dir):
    with open(os.path.join(output_dir,"lemmafinder_all_lemmas.txt"), "w") as f:
        f.write(json.dumps(content))

def write_op(lemma_file_name, output_dir):
    with open(os.path.join(output_dir,"lemmafinder_bench.txt"), "w") as f:
        f.write(json.dumps(lemma_file_name))


def main() -> None:
    args, parser = parse_arguments()
    if args.output is None:
        args.output = args.prelude
    no_coq_files, no_with_helper, total_lemmas, lemma_file_names, tactics_dict = count(args.prelude, args.output, args.project)
    write_op(lemma_file_names,args.output)
    print(dict(sorted(tactics_dict.items(), key=lambda x: x[1], reverse=True)))
    print(f"#Lemmas w atleast one helper/#Lemmas: {no_with_helper}/{total_lemmas} in {no_coq_files} coq files")


if __name__ == "__main__":
    main()

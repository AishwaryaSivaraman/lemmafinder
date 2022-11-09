import argparse
import os
import json
import shutil
import subprocess
import sys
import csv

from typing import Tuple

lfind_decl = "Load LFindLoad.\nFrom lfind Require Import LFind.\nUnset Printing Notations.\nSet Printing Implicit.\n"

def parse_arguments() -> Tuple[argparse.Namespace, argparse.ArgumentParser]:
    parser = argparse.ArgumentParser(
        description=
        "Run benchmark files")
    parser.add_argument('--prelude', default="./")
    parser.add_argument('--logical_directory', default="test")
    parser.add_argument('--log_directory', default="./")
    parser.add_argument('--debug', action='store_true')
    parser.add_argument('--example_dir', default=None)
    return parser.parse_args(), parser

def get_locations(folder):
    benchmark_file = os.path.join(folder, "lemmafinder_bench.txt")
    with open(benchmark_file, 'r') as j:
     lemma_dict = json.loads(j.read())    
    return lemma_dict

def get_all_lemmas(folder):
    benchmark_file = os.path.join(folder, "lemmafinder_all_lemmas.txt")
    with open(benchmark_file, 'r') as j:
     all_lemmas = json.loads(j.read())    
    return all_lemmas

def lemma_finder_copy(source_folder, dest_folder) -> None:
    print(dest_folder)
    if not os.path.isdir(dest_folder):
        shutil.copytree(source_folder, dest_folder)

def write_lemmafinder_content(file, content):
    print(file)
    with open(file,"w") as f:
        f.write("".join(content))

def write_errors_to_csv(csv_file, content):
    column_names = ["Original Statement", "Required Helper Lemma", "Make Cmd", "Stuck State"]
    with open(csv_file, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(column_names)
        writer.writerows(content)

def get_stuck_state(fname):
    try:
        with open(fname, 'r') as j:
            content = j.readlines()
            for l in content:
                if "lfind_state" in l:
                    return l
    except Exception as e:
        print(e)
    return ""

def run(source_folder, helper_lemma_dict, log_directory, all_lemmas_from_file, example_dir, debug=False):
    counter = 0
    all_lemmas = 0
    category_1_count = 0
    filtered_helper_lemma_dict = {}
    rewriter_failures = []
    invalid_ml_faulires =[]
    invalid_examples = []
    myth_parse_errors = []
    for file in helper_lemma_dict:
        file_name = os.path.basename(file)
        print(file_name)
        helper_lemma_locations = helper_lemma_dict[file]
        if ".v" in file :
            with open(file) as f:
                content = f.readlines()
            for location in helper_lemma_locations:
                print(location)      
                lemma_line = location[1]
                lemma_name = location[2].replace("'","")
                lfind_content = [lfind_decl]
                lfind_content.append("\n") 
                lfind_content.extend(content[:lemma_line])
                current_line = content[lemma_line]
                c_line_content = current_line.split(".")
                c_modified_content = []
                destination_name = str(os.path.basename(source_folder))+"_lf_" + os.path.splitext(file_name)[0] + "_" + location[0].replace("'","") + "_" + str(location[1])+ "_"+lemma_name

                destination_folder = os.path.join(os.path.dirname(source_folder),str(os.path.basename(source_folder))+"_lf_" + os.path.splitext(file_name)[0] + "_" + location[0].replace("'","") + "_" + str(location[1])+ "_"+lemma_name)

                stuck_folder = os.path.join(os.path.dirname(source_folder),"_lfind_" + str(os.path.basename(source_folder))+"_lf_" + os.path.splitext(file_name)[0] + "_" + location[0].replace("'","") + "_" + str(location[1])+"_" + lemma_name)
                lfind_summary_log = os.path.join(stuck_folder, "lfind_summary_log.txt")
                # is_run_make = True
                if os.path.isdir(stuck_folder) and os.path.isfile(lfind_summary_log):
                    print("found lfind summary");
                    continue
                    is_run_make = False
                else:
                    is_run_make = True
                lemma_finder_copy(source_folder, destination_folder)
                if example_dir:
                    src = os.path.join(example_dir, destination_name)
                    if os.path.isdir(src):
                        files=os.listdir(src)
                        for file in files:
                            shutil.copy2(os.path.join(src,file), destination_folder)
                for i in range(0,len(c_line_content)):
                    first_index_val = c_line_content[i].strip().split(" ")[0]
                    lfind_tactic = ""
                    if '*' in first_index_val or '-' in first_index_val or '+' in first_index_val or '{' in first_index_val:
                        lfind_tactic = first_index_val
                    if lemma_name in c_line_content[i]:
                        if debug:
                            c_modified_content.append(lfind_tactic + " lfind_debug")
                        else:
                            c_modified_content.append(lfind_tactic + " lfind")
                    else:
                        c_modified_content.append(c_line_content[i])
                lfind_content.append(". ".join(c_modified_content))
                lfind_content.append("Admitted.\n")
                next_valid_index_found = False
                index = lemma_line + 1
                while not next_valid_index_found:
                    if "Qed" in content[index] or "Admit" in content[index]:
                        next_valid_index_found = True
                    index = index + 1
                lfind_content.extend(content[index:])
                print(f"destination folder is {destination_folder}")
                write_lemmafinder_content(os.path.join(destination_folder, file_name),lfind_content)
                debug_log_folder = os.path.join(os.path.dirname(source_folder),"_lfind_" + str(os.path.basename(source_folder))+"_lf_" + os.path.splitext(file_name)[0] + "_" + location[0].replace("'","") + "_" + str(location[1]) + "_"+lemma_name)
                log_file = f"{debug_log_folder}/lfind_summary_log.txt"
                make_log_file = f"{log_directory}/lfind_benchmark_log"
                make_cmd = f"cd {destination_folder} && make > {make_log_file}"
                print(make_cmd)
                if not is_run_make:
                    result = ""
                else:
                    result=subprocess.getoutput(make_cmd)
                contents = ""
                try:
                    print(log_file)
                    contents = open(log_file).read()
                except:
                    print("error processing log file")
                all_lemmas+=1
                if "error" in result or "exception" in result:
                    try:
                        stuck_state_file = os.path.join(stuck_folder, "lfind_state.v")
                        stuck_state = get_stuck_state(stuck_state_file)
                        error_content = [all_lemmas_from_file[location[0]],all_lemmas_from_file[location[2]],make_cmd,stuck_state]
                        if "Rewrite_Fail" in result:
                            rewriter_failures.append(error_content)
                        elif "Invalid_MLFile" in result:
                            invalid_ml_faulires.append(error_content)
                        elif "Invalid_Examples" in result:
                            invalid_examples.append(error_content)
                        elif "lemmafinder_example_generation_success" in contents and "Parser.MenhirBasics.Error" in result:
                            myth_parse_errors.append(error_content)
                        else:
                            print(f"error is {result}")
                            # import sys
                            # sys.exit(0)
                    except Exception as e:
                        print(f"error processing {location} {e}")
                if "COMPLETED LFIND SYNTHESIZER" in contents:
                    print("Success: " + location[2])
                    # get log file and write it in the log_directory
                    try:
                        log_folder = os.path.join(os.path.dirname(source_folder),"_lfind_" + str(os.path.basename(source_folder))+"_lf_" + os.path.splitext(file_name)[0] + "_" + location[0].replace("'","") + "_" + str(location[1])+"_"+lemma_name)
                        lfind_summary_log = os.path.join(log_folder, "lfind_summary_log.txt")
                        lfind_log = os.path.join(log_folder, "lfind_log.txt")
                        with open(lfind_summary_log, 'r') as j:
                            lfind_log_content = j.read()
                        with open(lfind_summary_log, 'r') as j:
                            summary_content = j.readlines()
                            for l in summary_content:
                                if "Yes Cat 1: true" in l:
                                    category_1_count += 1
                        theorem_name = os.path.splitext(file_name)[0] + "_" + location[0]
                        helper_name = os.path.splitext(file_name)[0] + "_" + location[2]
                        content_to_append = f"Theorem statement:\n{all_lemmas_from_file[theorem_name]}\n\nRequired Helper Statement:\n{all_lemmas_from_file[helper_name]}\n"
                        lfind_log_w = os.path.join(log_directory, f"{os.path.splitext(file_name)[0]}_{location[0]}_{location[1]}_{location[2]}")
                        with open(lfind_log_w, "w") as w:
                            w.write(content_to_append)
                            w.write(lfind_log_content)
                            w.write(f"\nMore log here {lfind_log}\n")
                            w.write(f"Original Coq file here {file}\n")
                            w.close()
                        counter += 1
                        if file in filtered_helper_lemma_dict:
                            filtered_helper_lemma_dict[file].append(location)
                        else:
                            filtered_helper_lemma_dict[file] = [location]
                    except Exception as e:
                        print(f"error processing this {e}")
                else:
                    print("no success")
            write_lemmafinder_content(os.path.join(destination_folder, file_name),content)
    
    # Write errors to csv file
    print(f"#rewriter failures: {len(rewriter_failures)}\n")
    write_errors_to_csv(os.path.join(log_directory, "rewrite_failure.csv"), rewriter_failures)
    print(f"#invalid ml file failures: {len(invalid_ml_faulires)}\n")
    write_errors_to_csv(os.path.join(log_directory, "invalid_ml_failures.csv"), invalid_ml_faulires)
    print(f"#invalid example generation failures: {len(invalid_examples)}\n")
    write_errors_to_csv(os.path.join(log_directory, "invalid_example_failures.csv"), invalid_examples)
    print(f"#myth parse errors: {len(myth_parse_errors)}\n")
    write_errors_to_csv(os.path.join(log_directory, "myth_parse_failures.csv"), myth_parse_errors)
    
    return filtered_helper_lemma_dict, counter, all_lemmas, category_1_count

def main() -> None:
    args, parser = parse_arguments()
    helper_lemma_dict = get_locations(args.prelude)
    all_lemmas_from_file = get_all_lemmas(args.prelude)
    os.makedirs(args.log_directory, exist_ok=True)
    filtered_helper_lemmas, total_lemmas, all_lemmas, cat_1_count = run(args.prelude, helper_lemma_dict, args.log_directory, all_lemmas_from_file, args.example_dir, args.debug)
    print(filtered_helper_lemmas)
    print(f"#Lemmas that pass lemmafinder/#Lemmas: {total_lemmas}/{all_lemmas} in {len(filtered_helper_lemmas)} coq files")
    print(f"#Lemmas that contain category 1 results amongst the successful lemmas: {cat_1_count}/{total_lemmas} ")


if __name__ == "__main__":
    main()

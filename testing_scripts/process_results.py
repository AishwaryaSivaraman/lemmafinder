import os
import csv

# This file contains functions that are responsible for:
#   - parsing the lfind_summary_log for each benchmark
#   - write the results to a csv file for easy viewing
#   - clean up the generated folders (if the flag is set)
#       - returns project to original state (just coq files)
#       - clean -> removes all created files except for:
#                   ~ the new file with lfind in it
#                   ~ the lfind_summary_log.txt for each example
#                   ~ the log directory folder

def parse_contents(contents,all_lemmas,summary_path):
    result = {}
    result["Success"] = False
    result["RunTime"] = -1
    result["# of Cat 1"] = 0
    result["# of Cat 2"] = 0
    result["# of Cat 3"] = 0
    result["Generalization Count"] = 0
    result["Success"] = True
    try:
        f = open(summary_path, 'r')
        summary_content = f.readlines()
        category_1 = -1
        category_2 = -1
        category_2 = -1
        line_number = 0
        for line in summary_content:
            line_number += 1
            if "# Generalizations" in line:
                result["Generalization Count"] = line.split(":")[1]
            elif "(Category 1)" in line:
                category_1 = line_number
            elif "(Category 2)" in line:
                category_2 = line_number
            elif "(Category 3)" in line:
                category_3 = line_number
            elif "Total Time" in line:
                result["RunTime"] = line.split(":")[1]
        result["# of Cat 1"] = (category_2 - 1) - (category_1 + 1)
        result["# of Cat 2"] = (category_3 - 1) - (category_2 + 1)
        result["# of Cat 3"] = (line_number - 1) - (category_3 + 1)
    except:
        result["Success"] = False
    return result

def write_to_csv(csv_file, content):
    column_names = ["File", "Example", "Success", "RunTime", "# of Cat 1", "# of Cat 2", "# of Cat 3", "Generalization Count"]
    with open(csv_file, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(column_names)
        writer.writerows(content)

def clean_up_project(project_path,lfind_folder):
    remove = [f"rm -R {lfind_folder}"]
    for file in os.listdir(project_path):
        parts = file.split(".")
        if len(parts) != 2 or parts[1] != "v":
            remove.append(f"rm {os.path.join(project_path,file)}")
    for cmd in remove:
        os.system(cmd)

# Regardless of clean tags, this will move interesting information to logs folder
# If clean, will remove all folders created by lfind 
def clean_up_lfind(result_folders,log_directory,clean):
    for file in result_folders:
        for folder in result_folders[file]:
            summary = os.path.join(folder,"lfind_summary_log.txt")
            parent = os.path.dirname(folder)
            example_folder = os.path.basename(folder)
            example = example_folder[len("_lfind_"):]
            lfind_file = os.path.join(folder,file)
            new_folder = os.path.join(log_directory,example)
            # Make new folder (delete if it exists)
            if os.path.exists(new_folder) == False:
                os.mkdir(new_folder)
            # Move the lfind file and results file to folder
            os.system(f"mv -f {lfind_file} {new_folder}")
            os.system(f"mv -f {summary} {new_folder}")
            # Delete the produced folders if cleaning
            if clean:
                os.system(f"rm -R {folder}")
                og_lfind_folder = os.path.join(parent,example)
                os.system(f"rm -R {og_lfind_folder}")

def process_results(result_folders,log_directory,all_lemmas,clean):
    content_for_csv = []
    for file in result_folders:
        for folder in result_folders[file]:
            summary = os.path.join(folder,"lfind_summary_log.txt")
            contents = None
            example_folder = os.path.basename(folder)
            example = example_folder[len("_lfind_"):]
            try:
                contents = open(summary).read()
            except:
                contents = None
                print(f"--- Error processing log file {summary}")
                try:
                    log_file = os.path.join(log_directory,f"lfind_benchmark_log_{example}")
                    log_contents = open(log_file).read()
                    if "lemmafinder_example_generation_success" not in log_contents:
                        print("---- Not able to succcessfully generate examples.")
                    else:
                        print("---- Not able to complete running.")
                except:
                    print("---- Log not generated properly.")
            if contents is not None:
                content_results = parse_contents(contents,all_lemmas,summary)
                content_for_csv.append([
                    file,
                    example, 
                    content_results["Success"], 
                    content_results["RunTime"], 
                    content_results["# of Cat 1"], 
                    content_results["# of Cat 2"], 
                    content_results["# of Cat 3"], 
                    content_results["Generalization Count"]
                ])
    clean_up_lfind(result_folders,log_directory,clean)
    return content_for_csv
            
import os
import json

# This file includes functions is in charge of: 
#   - ensuring that only coq .v files are in the project folder
#   - creating a _CoqProject for those files
#   - creating the necessary make files
#   - running make in that folder
#   - running collect scripts to generate the lists of lemmas and helper lemmas
#   - command lines below for Linux-based terminal (not sure if same commands will work for windws machines)

def create_CoqProject(files,namespace):
    content = []
    content.append(f"-R . {namespace}")
    content.append("\n")
    for file in files:
        content.append("\n")
        content.append(file)
    return content

def write_content_to_file(file, content):
    f = open(file,"w")
    f.write("".join(content))

def prepare_project(path):
    # Ensure that path only contains COQ files
    files = []
    for file in os.listdir(path):
        parts = file.split(".")
        if len(parts) == 2 and parts[1] == "v":
            files.append(file)
        else:
            print("Non-COQ files or directories in folder provided.")
            return False
    # Get _CoqProject Files
    namespace = os.path.basename(path)
    coqproject_contents = create_CoqProject(files,namespace)
    CoqProject = os.path.join(path,"_CoqProject")
    write_content_to_file(CoqProject,coqproject_contents)
    return True

def create_makefiles(path):
    os.system(f"cd {path} && coq_makefile -f _CoqProject -o Makefile")

def make_project(path):
    os.system(f"cd {path} && make")

# Assuming that the project folder is in the same folder as collect_stats.py
def collect_stats(path,lemmafinder):
    testing_script_folder = os.path.join(lemmafinder,"testing_scripts")
    collect_stat = os.path.join(testing_script_folder,"collect_stats.py")
    os.system(f"cd {path} && python3 {collect_stat}")

def get_helper_lemmas(folder):
    benchmark_file = os.path.join(folder, "lemmafinder_bench.txt")
    with open(benchmark_file, 'r') as j:
     lemma_dict = json.loads(j.read())    
    return lemma_dict

def get_all_lemmas(folder):
    benchmark_file = os.path.join(folder, "lemmafinder_all_lemmas.txt")
    with open(benchmark_file, 'r') as j: # This line will throw and error if this text file does not exist 
     all_lemmas = json.loads(j.read())    
    return all_lemmas

def remove_backslash(path):
    if path[len(path)-1] == "/":
        return path[:len(path)-1]
    else:
        return path

# This is the main function that executes all of the functions in the correct order
def prepare(project_path,cwd):
    project_path = remove_backslash(project_path)
    success = prepare_project(project_path)
    if success:
        create_makefiles(project_path)
        make_project(project_path)
        collect_stats(project_path,cwd)
        helper_lemmas = get_helper_lemmas(project_path)
        all_lemmas = get_all_lemmas(project_path)
        return helper_lemmas, all_lemmas
    else:
        return None, None
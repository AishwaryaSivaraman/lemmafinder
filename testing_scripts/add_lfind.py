import os
import shutil

# This file includes functions in charge of:
#   - takes in list of the files that include helper lemmas that are used
#   - create a new folder for each instance that a helper lemma is used
#   - move all relevant files to that folder (i.e. _CoqProject, MakeFiles, etc.)
#   - modify the coq .v file in the folder to include lfind at specified location (based on testing parameters)
#   - maintain a list of folders that have been created (all stored within a folder _LFIND_FILES for organization purposes)

def write_content_to_file(file, content):
    f = open(file,"w")
    f.write("".join(content))

# This function should return the paths to the folders that have lfind invoked for a given file, as well as the corresponding
# contents of those files.
def add_lfind(file,usages,path,parameters):
    folders = {}
    file_obj = open(os.path.join(path,file))
    content = file_obj.readlines()
    for use in usages:
        helper = use[2].replace("'","")
        line = use[1]
        theorem = use[0].replace("'","")
        # Start putting lfind content into file (i.e. the contents for the file)
        lfind_content = ["Load LFindLoad.\nFrom lfind Require Import LFind.\nUnset Printing Notations.\nSet Printing Implicit.\n"]
        lfind_content.append(parameters)
        lfind_content.append("\n")
        lfind_content.extend(content[:line])
        # At the line invoked, split up the tactics to figure out where lfind should be invoked
        line_contents = content[line].split(".")
        new_line = []
        for command in line_contents:
            if helper in command:
                # See if there is a COQ tactic used to make sure it stays consistent
                first_index_val = command.strip().split(" ")[0]
                lfind_tactic = ""
                if '*' in first_index_val or '-' in first_index_val or '+' in first_index_val or '{' in first_index_val:
                    lfind_tactic = first_index_val
                # Here we will add the specific parameters to lfind in order to run a specific way
                new_line.append(lfind_tactic + f" lfind.")
                break
            else:
                new_line.append(f"{command}")
        lfind_content.append(".".join(new_line))
        lfind_content.append(" Admitted.\n")
        # Now, we want to fill in the rest of the proof, following the point that the helper lemma is applied
        next_valid_index_found = False
        index = line + 1
        while not next_valid_index_found:
            # Notice this is looking within the original COQ file (without LFind invoked)
            # Checks if the proof is completed or admitted
            if "Qed" in content[index] or "Admit" in content[index]:
                next_valid_index_found = True
            index = index + 1
        # This adds the rest of the coq file that follows the proof with the helper lemma
        lfind_content.extend(content[index:])
        folders[f"{helper}.{line}.{theorem}"] = lfind_content
    return folders

def lemma_finder_copy(source_folder, dest_folder) -> None:
    if not os.path.isdir(dest_folder):
        shutil.copytree(source_folder, dest_folder)

def create_lfind_directories(file, usages, project_path,lfind_folder):
    # Get the file name, parent folder, and the project name
    file_name = file[:len(file)-2]
    project = os.path.basename(project_path)
    folders = []
    # Go through each usage, create a folder and populate it
    for use in usages:
            split = f"{use}".split(".")
            content = usages[use]
            helper = split[0]
            line = split[1]
            theorem = split[2]
            new_folder_name = f"{project}_{file_name}_{helper}_at{line}"
            new_folder = os.path.join(lfind_folder,new_folder_name)
            # Copy over the files
            lemma_finder_copy(project_path,new_folder)
            # Write the new coq file (with the lfind tactic used)
            write_content_to_file(os.path.join(new_folder, file),content)
            folders.append(new_folder)
    return folders
        
def invoke_lfind(helper_lemmas,project_path,lfind_parameters):
    contents = {}
    folders = {}
    parent = os.path.dirname(project_path)
    project_name = os.path.basename(project_path)
    lfind_folder = os.path.join(parent,f"{project_name}_LFIND_FILES")
    if os.path.exists(lfind_folder):
        os.system(f"rm -R {lfind_folder}")
    os.mkdir(lfind_folder)
    # Add lfind to each of the files where a helper lemma is used
    for file in helper_lemmas:
        contents[file] = add_lfind(file,helper_lemmas[file],project_path,lfind_parameters)
    # Create and fill folders for each instance that a counter example is use
    for file in contents:
        folders[file] = create_lfind_directories(file,contents[file],project_path,lfind_folder)
    # Returns a list of the folders that are created with lfind for each file
    return folders, lfind_folder
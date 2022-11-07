import argparse
import os
import shutil
from typing import Tuple

# Helper Functions that we created and run
from prepare import prepare
from add_lfind import invoke_lfind
from run_lfind import run_lfind
from process_results import process_results, clean_up_project, write_to_csv

# These are the defaul values, can be modified by user/tester to represent how they want lfind ran
def set_lfind_parameters():
    return {
        "debug" : 1, # 0 for off, 1 for on : int
        "synthesizer" : "coqsynth", # name of synthesizer : string
        "size" : 6, # max size of synthesized expressions : int
        "timeout" : 12 # timeout for synthesizer : int
    }

def parse_arguments() -> Tuple[argparse.Namespace, argparse.ArgumentParser]:
    parser = argparse.ArgumentParser(
        description=
        "Run Benchmark Files")
    parser.add_argument('--parent', default=None)
    parser.add_argument('--result_folder', default=None)
    parser.add_argument('--file', default=None)
    parser.add_argument('--project', default=None)
    parser.add_argument('--benchmarks', default=None)
    parser.add_argument('--clean', default=False, action='store_true')
    return parser.parse_args()

def run_on_project(project_path,log_directory,cwd):
    # Run all pre-processing
    helper_lemmas, all_lemmas = prepare(project_path,cwd)
    if helper_lemmas == None:
        return None, None, None, None
    # Create folders for each of the examples
    lfind_folders, lfind_folder = invoke_lfind(helper_lemmas,project_path,lfind_parameters=set_lfind_parameters())
    # Set log directory if not provided
    log_folder = log_directory if log_directory is not None else os.path.join(os.path.dirname(lfind_folder),"RESULTS")
    if os.path.isdir(log_folder) == False:
        os.mkdir(log_folder)
    # Run lfind for each file and get the results
    result_files = {}
    for file in lfind_folders:
        result_files[file] = run_lfind(lfind_folders[file],log_folder)
    return result_files, log_folder, all_lemmas, lfind_folder

def main() -> None:
    args = parse_arguments()
    cwd = os.path.abspath(os.getcwd())
    file_input = args.file
    project_input = args.project
    parent_dir = args.parent
    result_folder = args.result_folder
    benchmarks = [item for item in args.benchmarks.split(',')] if args.benchmarks is not None else []
    clean = args.clean

    if project_input is not None:
        # Make sure the path is absolute and exists
        try:
            project_path = os.path.abspath(project_input)
        except:
            print("Path provided doesn't exist. Try again.")
            return None
        # Run for the project and get the result folders
        result, result_folder, lemmas, lfind_folder = run_on_project(project_path=project_path,log_directory=result_folder,cwd=cwd)
        # Process the results
        if result is not [] and result is not None:
            csv_content = process_results(result,result_folder,lemmas,clean)
            write_to_csv(os.path.join(result_folder,"summary_log.csv"),csv_content)
            if clean:
                clean_up_project(project_path, lfind_folder)
        else:
            print(f"No results for {project_path}")
    elif file_input is not None:
        # Make sure the path is absolute
        try:
            file_path = os.path.abspath(file_input)
        except:
            print("Path provided doesn't exist. Try again.")
            return None
        # Create a folder with the file
        if os.path.isfile(file_path):
            file = f"{os.path.basename(file_path)}"
            parent = os.path.dirname(file_path)
            file_name = file.split(".")[0]
            directory = os.path.join(parent,file_name)
            os.mkdir(directory)
            shutil.copy(file_path,directory)
            # We can then pass this folder into the run_on_project function
            result, result_folder, lemmas, lfind_folder = run_on_project(project_path=directory,log_directory=result_folder,cwd=cwd)
            # Process the results
            if result is not [] and result is not None:
                csv_content = process_results(result,result_folder,lemmas,clean)
                write_to_csv(os.path.join(result_folder,"summary_log.csv"),csv_content)
                if clean:
                    clean_up_project(directory, lfind_folder)
            else:
                print(f"No results for {directory}")
        else:
            print("File input not a file.")
    elif parent_dir is not None and benchmarks is not []:
        # Make sure the parent path is absolute
        try:
            parent_path = os.path.abspath(parent_dir)
        except:
            print("Path provided doesn't exist. Try again.")
            return None
        # Run for each benchmark
        csv_content = []
        log_folder = result_folder if result_folder is not None else os.path.join(parent_path,"RESULTS")
        for bench in benchmarks:
            bench = f"{bench}".strip()
            # Make sure that bench folder exists
            bench_path = os.path.join(parent_path,bench)  
            if os.path.isdir(bench_path):
                result, result_folder, lemmas, lfind_folder = run_on_project(project_path=bench_path,log_directory=log_folder,cwd=cwd)
                if result is not [] and result is not None:
                    p = process_results(result,result_folder,lemmas,clean)
                    csv_content.append(p)
                    if clean:
                        clean_up_project(bench_path,lfind_folder)
                else:
                    print(f"No results for {bench}")
        if csv_content != []:
            write_to_csv(os.path.join(log_folder,"summary_log.csv"),csv_content)
    else:
        print("No inputs given. Try one options below:")
        print("--project={absolute path to directory of coq .v files}")
        print("--file={absolute path to single coq .v file}")
        print("--parent={absolute path to directory that holds project folder} --benchmarks={list of project folder names}")
        return None

if __name__ == "__main__":
    main()
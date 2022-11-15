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
def set_lfind_parameters(args):
    quickchick = "Unset Lfind Quickchick.\n" if args.no_quickchick else ""
    proverbot = "Unset Lfind Proverbot.\n" if args.no_proverbot else ""
    synth_size = f"Set Lfind BatchSize \"{args.synth_batch_size}\".\n" if args.synth_batch_size != 6 else ""
    # Here we just check if it's myth or not because we only consider one other synthesizer
    synthesizer = f"Set Lfind Synthesizer \"{args.synthesizer}\".\n" if args.synthesizer == "myth" else ""
    timeout = f"Set Lfind Batch-Size \"{args.synth_timeout}\".\n" if args.synth_timeout != 12 else ""
    return f"{quickchick}{proverbot}{synthesizer}{synth_size}{timeout}"

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
    parser.add_argument('--no_quickchick', default=False, action='store_true')
    parser.add_argument('--no_proverbot', default=False, action='store_true')
    parser.add_argument('--synth_batch_size', default=6, type=int)
    parser.add_argument('--synth_timeout', default=12, type=int)
    parser.add_argument('--synthesizer', default="coqsynth")
    parser.add_argument('--rerun', default=False, action='store_true')
    parser.add_argument('--lfind_files', default=None)
    return parser.parse_args()

def run_on_project(project_path,log_directory,cwd,parameters):
    # Run all pre-processing
    helper_lemmas, all_lemmas = prepare(project_path,cwd)
    if helper_lemmas == None:
        return None, None, None, None
    # Create folders for each of the examples
    lfind_folders, lfind_folder = invoke_lfind(helper_lemmas,project_path,lfind_parameters=parameters)
    # Set log directory if not provided
    log_folder = log_directory if log_directory is not None else os.path.join(os.path.dirname(lfind_folder),"RESULTS")
    if os.path.isdir(log_folder) == False:
        os.mkdir(log_folder)
    # Run lfind for each file and get the results
    result_files = {}
    for file in lfind_folders:
        result_files[file] = run_lfind(lfind_folders[file],log_folder)
    # Returns result files (by file name and stores list of result folders), log folder, list of all lemmas, lfind folder
    return result_files, log_folder, all_lemmas, lfind_folder

def resume_run_on_project(lfind_files,log_directory):
    if os.path.isdir(log_directory) == False:
        os.mkdir(log_directory)
    # Run lfind for each file and get the results
    result_folders = [] # These are the lfind_summary_log.txt files as the values, and the key is the example
    delete = []
    not_result = []
    examples = []
    # Figure out which folders need to be ran
    for folder in os.listdir(lfind_files):
        if folder.startswith("_lfind_"):
            log_path = os.path.join(os.path.join(lfind_files,folder),"lfind_summary_log.txt")
            if os.path.exists(log_path):
                print(f"Re-using:{log_path}")
                # Get example name
                result_folders.append(os.path.join(lfind_files,folder)) # Need to use the absolute path
                examples.append(folder[len("_lfind_"):])
            else:
                print(f"Deleting: {os.path.join(lfind_files,folder)}")
                delete.append(f"rm -R {os.path.join(lfind_files,folder)}")
        else:
            not_result.append(folder)
    # Delete the lfind folders that are incomplete (should just be one)
    for cmd in delete:
        os.system(cmd)
    # Run the other folders, if their lfind folder does not exist
    to_run = []
    for folder in not_result:
        if folder not in examples:
            to_run.append(os.path.join(lfind_files,folder))
    result_folders.extend(run_lfind(folders=to_run,log_dir=log_directory))
    # Return result folder
    return result_folders
    
def main() -> None:
    args = parse_arguments()
    cwd = os.path.abspath(os.getcwd())
    file_input = args.file
    project_input = args.project
    parent_dir = args.parent
    result_folder = args.result_folder
    benchmarks = [item for item in args.benchmarks.split(',')] if args.benchmarks is not None else []
    clean = args.clean
    lfind_files = args.lfind_files
    parameters = set_lfind_parameters(args)

    if args.rerun:
        # This option processes the logs differently (because we don't maintain access to which file had created it)
        # This will be dependent on how we want to log outputs and what information we want from the lfind_summary_log.txt
        # Also the results will not be processed in the same way... again this can be changed when it is needed
        if result_folder is None or lfind_files is None or os.path.exists(lfind_files) == False:
            print("In order to rerun, you need to have a result folder and you need to pass in the project LFIND_FILES folder.")
            return None
        # Run for the project and get the result folders
        result = resume_run_on_project(lfind_files=lfind_files,log_directory=result_folder)
        # Now there should be a bunch of lfind_summary_log.txt files in the folders with no processing done
        print("The result folder will not be processed/organized the same as non-rerun options. And, --clean flag is ineffecitve.")
        print("The folders below hold the results from running lfind on the examples:")
        print(result)
    elif project_input is not None:
        # Make sure the path is absolute and exists
        try:
            project_path = os.path.abspath(project_input)
        except:
            print("Path provided doesn't exist. Try again.")
            return None
        # Run for the project and get the result folders
        result, result_folder, lemmas, lfind_folder = run_on_project(project_path=project_path,log_directory=result_folder,cwd=cwd, parameters=parameters)
        # Process the results
        if result is not [] and result is not None:
            csv_content = process_results(result,result_folder,clean)
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
            result, result_folder, lemmas, lfind_folder = run_on_project(project_path=directory,log_directory=result_folder,cwd=cwd,parameters=parameters)
            # Process the results
            if result is not [] and result is not None:
                csv_content = process_results(result,result_folder,clean)
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
                result, result_folder, lemmas, lfind_folder = run_on_project(project_path=bench_path,log_directory=log_folder,cwd=cwd,parameters=parameters)
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
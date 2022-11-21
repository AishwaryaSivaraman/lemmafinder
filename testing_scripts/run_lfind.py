import os
import subprocess

# This file includes functions in charge of:
#   - running make on each of the folders with lfind
#   - keeping track of the folders that holds the results
#   - returns a list of the folders prodcued by lfind (starting with _lfind_...)

def results_folder(lfind_folder):
    parent = os.path.dirname(lfind_folder)
    folder_name = os.path.basename(lfind_folder)
    return os.path.join(parent,f"_lfind_{folder_name}")

# Returning a list of the folders that lfind is in and were made
def run_lfind(folders,log_dir):
    results = []
    for folder in folders:
        folder_name = os.path.basename(folder)
        make_log_file = f"{log_dir}/lfind_benchmark_log_{folder_name}"
        os.system(f"touch {make_log_file}")
        make_cmd = f"cd {folder} && make > {make_log_file}"
        try:
            run = subprocess.getoutput(make_cmd)
            print(f"Ran lfind for {folder_name}")
        except:
            os.system(make_cmd) # Sometimes the subprocess.getoutput throws errors, use this instead if so
        results.append(results_folder(folder))
    return results
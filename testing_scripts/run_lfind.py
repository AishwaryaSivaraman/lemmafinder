import os
import subprocess

# This file includes functions in charge of:
#   - running make on each of the folders with lfind
#   - keeping track of the folders that holds the results
#   - returns a list of the lfind_summary_log.txt absolute paths for file

def results_folder(lfind_folder):
    parent = os.path.dirname(lfind_folder)
    folder_name = os.path.basename(lfind_folder)
    return os.path.join(parent,f"_lfind_{folder_name}")

# Not entirely sure what the significance is for these errors, this portion was pulled from prior script
def check_for_errors(result,folder):
    err = False
    if "error" in result or "exception" in result:
        err = True
        try:
            if "Rewrite_Fail" in result:
                print("Rewrite Error")
            elif "Invalid_MLFile" in result:
                print("Invalid ML File Error")
            elif "Invalid_Examples" in result:
                print("Some quickchick error")
            elif  "Parser.MenhirBasics.Error" in result:
                print("Potential Myth Parse Error")
            else:
                print(f"error is {result}")
        except Exception as e:
            print(f" processing {folder} {e}")
    return err

# Returning a list of the folders that lfind is in and were made
def run_lfind(folders,log_dir):
    results = []
    for folder in folders:
        folder_name = os.path.basename(folder)
        make_log_file = f"{log_dir}/lfind_benchmark_log_{folder_name}"
        os.system(f"touch {make_log_file}")
        make_cmd = f"cd {folder} && make > {make_log_file}"
        result = subprocess.getoutput(make_cmd)
        error = check_for_errors(result,folder)
        #os.system(make_cmd) # Sometimes the subprocess.getoutput throws errors, use this instead if so
        results.append(results_folder(folder))
    return results
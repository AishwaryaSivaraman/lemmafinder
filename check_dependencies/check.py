import os
import subprocess
import argparse

files_to_keep = ["Makefile","Makefile.conf","_CoqProject"]

def check_proverbot(printing):
    # Make sure that the Proverbot path is set up
    prover_path = os.environ.get("PROVERBOT")
    if prover_path == None:
        print(" * Proverbot path not set up properly.")
        print("     --> be sure to clone Proverbot from \"https://github.com/UCSD-PL/proverbot9001\"")
        return False

    # Start to attempt to execute, first get the command
    script = os.path.join(os.path.join(prover_path,"src"),"search_file.py")
    weights = os.path.join(os.path.join(prover_path,"data"),"polyarg-weights.dat")
    prelude = os.path.join(os.path.dirname(os.path.realpath(__file__)),"proverbot_example")
    files = [("test_one",False),("test_two",True)]

    # Need to compile the coq projects first
    subprocess.getoutput(f"cd {prelude} && make")
    cmds = []
    for file,result in files:
        report_path = os.path.join(prelude,f"search-report-{file}")
        cmd = f"timeout 30 python3 {script} --prelude={prelude} --weightsfile={weights} {file}.v --no-generate-report --max-proof-time=15 -P -o {report_path}"
        cmds.append((cmd,result,report_path,file))

    # Now we want to run the command to ensure that Proverbot is working
    check = True
    for cmd,exp,result_path,file in cmds:
        output_initial = subprocess.getoutput(cmd)

        # Process the results to see if Proverbot was able to run... specifically what may be causing any error
        if "ModuleNotFoundError: No module named 'coq_serapy'" in output_initial:
            print(" * CoqSerapy Module is not installed.")
            print("     --> be sure to run \"make setup\" in the Proverbot directory to install all needed dependencies.")
            print("         --> you may need to run \"cd {coq-synth path} && opam install . --deps-only && dune build && dune install\" again to update dependencies.")
            check = False
            break
        elif f"FileNotFoundError: [Errno 2] No such file or directory: '{prover_path}/data/polyarg-weights.dat'" in output_initial:
            print(" * Weights not initialized for Proverbot")
            print("     --> be sure to run \"make download-weights\" in the Proverbot directory.")
            check = False
            break
        else:
            if "command not found: sertop" in output_initial:
                print(" * Opam dependencies for Proverbot not downloaded properly.")
                check = False
                break
            dependencies = ["scikit-learn","sexpdata","torch","torchvision","yattag","pampy","pygraphviz","tqdm","pathlib_revised","sparse_list","tensorboard","maturin"]
            for d in dependencies:
                if f"ModuleNotFoundError: No module named '{d}'" in output_initial:
                    print(f" * {d} has not been added to the pip enivornment. [Proverbot dependency]")
                    print("     --> be sure to run \"make setup\" in the Proverbot directory to install all needed dependencies.")
                    print(f"     --> can independently install with command: \"pip install --user {d}.")
                    print("     --> ensure that the version of pip that you're using (or that is in setup.sh is compatible with your version of python")
                    check = False
                    break
            if check == False: break
            if "ModuleNotFoundError: No module named 'dataloader'" in output_initial or "command not found: rustup" in output_initial:
                print(" * Rust didn't compile. [Proverbot dependency]")
                print("     --> try running command: \"rustup toolchain install nightly\"")
                check = False
                break
        
        # See if the information is correct
        result_file = os.path.join(result_path,f"{file}-proofs.txt")
        process_cmd= f"cat {result_file} | grep SUCCESS | grep {file} -c"
        output = subprocess.getoutput(process_cmd)
        provable = output == '1'
        check = check and (provable == exp)
    
    # Report results
    if not check:
        print(" * Error running Proverbot.")

    # Clean out the create files
    remove = []
    for item in os.listdir(prelude):
        if item not in files_to_keep and not item.endswith(".v"):
            remove.append(item)
    for item in remove: os.system(f"rm -R {os.path.join(prelude,item)}")

    if not check and printing:
        print("Output from running Proverbot:")
        print(output_initial)

    return check

def check_coqsynth(printing):
    # Make sure the example that we are testing on is compiled
    # (This step might not be necessary if we are using the same example that is already compiled)
    dir = os.path.dirname(os.path.realpath(__file__))
    example_dir = os.path.join(dir,"coqsynth_example")
    make_cmd = f"cd {example_dir} && make"
    subprocess.getoutput(make_cmd)

    # Create the command to run coq-synth
    examples = "'Nil,4=Cons 4 Nil;Cons 1 (Cons 0 Nil),2=Cons 2 (Cons 0 (Cons 1 Nil));Cons 1 (Cons 2 Nil),1=Cons 1 (Cons 2 (Cons 1 Nil))'"
    num_terms = 5
    extra_exprs = "append,rev"
    params = "l1:lst,n:nat"
    type = "lst"
    module = "list_rev"
    logic_dir = "lia"
    cmd = f"coq_synth --logical-dir={logic_dir} --physical-dir=\"{example_dir}\" --module={module} --type={type} --params={params} --extra-exprs={extra_exprs} --examples={examples} --num-terms={num_terms}"

    # Run the coq-synth command and get the output
    output = subprocess.getoutput(cmd)
    expected_output = "(Cons n (rev l1))\n(Cons n (append (rev l1) Nil))\n(rev (append (rev (rev l1)) (Cons n Nil)))\n(rev (append l1 (Cons n Nil)))\n(Cons n (rev (append l1 Nil)))"

    # Returns whether or not the outputs are equal
    result = output == expected_output
    if not result:
        print(" * Coq-Synth is not set up properly.")
        print("     --> be sure to clone coq-synth from \"https://github.com/qsctr/coq-synth\"")
        print("     --> run the command: \"cd {coq-synth path} && opam install . --deps-only && dune build && dune install")
        print("     --> if another version of coq is pinned run: \"opam pin add coq 8.11.0\" or a new version of coq")
        if printing:
            print("CoqSynth Output from running:")
            print(output)

    # Clean out the create files
    remove = []
    for file in os.listdir(example_dir):
        if file not in files_to_keep and not file.endswith(".v"):
            remove.append(file)
    for item in remove: os.system(f"rm -R {os.path.join(example_dir,item)}")

    return result

def check_myth():
    myth_path = os.environ.get("MYTH")
    if myth_path == None:
        print(" * Myth path not set up properly.")
        return False
    return True

def check_other_paths():
    result = True
    # Check that LFind path is set
    expected_lfind_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
    lfind_path = os.environ.get("LFIND")
    if lfind_path == None or lfind_path != expected_lfind_path:
        print(" * Incorrct LFind path or path not set up properly.")
        result = False
    # Check COQOFOCAML
    coq_of_ocaml_path = os.environ.get("COQOFOCAML")
    if coq_of_ocaml_path == None:
        print(" * COQ of OCAML path not set up properly.")
        result = False
    return result

def driver():
    parser = argparse.ArgumentParser()
    parser.add_argument('--print', default=False, action='store_true')
    result = check_other_paths()
    result = check_proverbot(parser.parse_args().print) and result
    result = check_coqsynth(parser.parse_args().print) and result
    # result = check_myth() and result # Might not be necessary if we are moving forward with coq-synth

    if result:
        print("All external dependencies seem to be set up properly.")
    else:
        print("At least one external dependency is not running properly.")
    
    # Return the result (i.e. if the external tools are behaving as expected)
    return result


if __name__ == "__main__":
    driver()
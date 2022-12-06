import os
import subprocess

def check_proverbot():
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
    cmds = []
    for file,result in files:
        report_path = os.path.join(prelude,f"search-report-{file}")
        cmd = f"timeout 30 python3 {script} --prelude={prelude} --weightsfile={weights} {file}.v --no-generate-report --max-proof-time=15 -P -o {report_path}"
        cmds.append((cmd,result,report_path,file))

    # First need to clear out previous attempts to run the testing script
    dir_to_delete = []
    for item in os.listdir(prelude):
        if item.startswith("search-report-"):
            dir_to_delete.append(os.path.join(prelude,item))
    for dir in dir_to_delete: os.system(f"rm -R {dir}")

    # Now we want to run the command to ensure that Proverbot is working
    check = True
    for cmd,exp,result_path,file in cmds:
        output_initial = subprocess.getoutput(cmd)

        # Process the results to see if Proverbot was able to run
        if "ModuleNotFoundError: No module named 'coq-serapy'" in output_initial:
            print(" * CoqSerapy Module is not installed.")
            print("     --> be sure to run \"make setup\" in the Proverbot directory.")
            return False
        
        # See if the information is correct
        result_file = os.path.join(result_path,f"{file}-proofs.txt")
        process_cmd= f"cat {result_file} | grep SUCCESS | grep {file} -c"
        output = subprocess.getoutput(process_cmd)
        provable = output == '1'
        check = check and (provable == exp)
    
    # Report results
    if not check:
        print(" * Ran Proverbot successfully, but results were incorrect.")
    return check

def check_coqsynth():
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
    result = check_other_paths()
    result = check_proverbot() and result
    result = check_coqsynth() and result
    # result = check_myth() and result # Might not be necessary if we are moving forward with coq-synth
    if result:
        print("All external dependencies seem to be set up properly.")
    else:
        print("At least one external dependency is not running properly.")


if __name__ == "__main__":
    driver()
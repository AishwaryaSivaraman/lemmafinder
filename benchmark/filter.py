
import multiprocessing
from functools import partial
import coq_serapy
import sys
import argparse
from multiprocessing import set_start_method
set_start_method("spawn", force=True)

def parse_arguments():
    parser = argparse.ArgumentParser(
        description=
        "Rank and Generate CSV")
    parser.add_argument('--prelude', default=".")
    parser.add_argument('--theorem_name', default=".")
    parser.add_argument('--theorem', default=".")
    parser.add_argument('--lemmas', nargs = "*", type=str, default=[])
    parser.add_argument('--imports', nargs = "*", type=str, default=[])
    return parser.parse_args(), parser

def is_trivial(lemma, prelude, imports):
    proof_cmds = [lemma+".", "Proof.",
        "trivial.",
        "Qed."]
    with coq_serapy.SerapiContext(
            ["sertop", "--implicit"],    
            None,
            prelude) as coq:
        for imp in imports:
            coq.run_stmt(imp)
        cmds_left, cmds_run = coq.run_into_next_proof(
            proof_cmds)
        try:
            _, _ = coq.finish_proof(cmds_left)
            return True
        except coq_serapy.CoqExn:
            return False 

def is_eq(expr):
    return "eq" in expr
    # import re
    # match = re.match('([^,]*,)?[ ]?eq[]', expr)
    # return match

def simplify_lemma(lemma, prelude, imports):
    lemmaname = lemma.split(":")[0]
    with coq_serapy.SerapiContext(
            ["sertop", "--implicit"],    
            None,
            prelude) as coq:
        for imp in imports:
            coq.run_stmt(imp)
        coq.run_stmt(lemma + ".")
        coq.run_stmt("intros.")
        coq.run_stmt("simpl.")
        if is_eq(coq.goals):
            body = coq.goals.split("eq")[1].strip()
            if body[0] == "(":
                parans = 1
                for i in range(1, len(body)):
                    if parans == 0:
                        left, right = body[:i].strip(), body[i:].strip()
                        break
                    elif body[i] == ")":
                        parans -= 1
                    elif body[i] == "(":
                        parans += 1
                pass
            else:
                left, right = body.split(" ", 1)
            if len(left) > len(right):
                coq.run_stmt("symmetry.")
        return lemmaname, coq.goals.strip()

def is_proof_complete(prelude, imports, proof_cmds, stmts=[]):
    print(proof_cmds)
    with coq_serapy.SerapiContext(
            ["sertop", "--implicit"],    
            None,
            prelude) as coq:
        for imp in imports:
            coq.run_stmt(imp)
        for stmt in stmts:
            coq.run_stmt(stmt)
        try:
            cmds_left, cmds_run = coq.run_into_next_proof(
            proof_cmds)
            _, _ = coq.finish_proof(cmds_left)
            return True
        except coq_serapy.CoqExn:
            return False 
        except:
            return False

def is_weaker_than_human(human_lemma_name, synth_lemma, prelude, imports):
    if synth_lemma[len(synth_lemma)-1] == ".":
        name =  synth_lemma 
    else:
        name =  synth_lemma+"."
    apply_proof_cmds = [name, "Proof.",
        "intros.",
        f"apply {human_lemma_name}.",
        "Qed."]
    is_proof_complete_apply = is_proof_complete(prelude, imports, apply_proof_cmds)
    rewrite_proof_cmds = [name, "Proof.",
        "intros.",
        f"rewrite -> {human_lemma_name}.",
        "reflexivity.",
        "Qed."]
    is_proof_complete_rewrite = is_proof_complete(prelude, imports, rewrite_proof_cmds)
    rewrite_proof_cmds = [name, "Proof.",
        "intros.",
        f"rewrite <- {human_lemma_name}.",
        "reflexivity.",
        "Qed."]
    is_proof_complete_rewrite_left = is_proof_complete(prelude, imports, rewrite_proof_cmds)
    return is_proof_complete_apply or is_proof_complete_rewrite or is_proof_complete_rewrite_left

def is_stronger_than_human(human_lemma_name, human_lemma, synth_lemma, prelude, imports):
    synth_lemma_name = synth_lemma.split(":")[0].replace("Lemma ", "").strip()
    if synth_lemma[len(synth_lemma)-1] == ".":
        stmts = [synth_lemma, "Admitted."]
    else:
        stmts = [synth_lemma+".", "Admitted."]
    apply_proof_cmds = [human_lemma.replace(human_lemma_name, "humanlemma"), "Proof.",
        "intros.",
        f"apply {synth_lemma_name}.",
        "Qed."]
    is_proof_complete_apply = is_proof_complete(prelude, imports, apply_proof_cmds, stmts)
    rewrite_proof_cmds = [human_lemma.replace(human_lemma_name, "humanlemma"), "Proof.",
        "intros.",
        f"rewrite -> {synth_lemma_name}.",
        "reflexivity.",
        "Qed."]
    is_proof_complete_rewrite = is_proof_complete(prelude, imports, rewrite_proof_cmds, stmts)
    rewrite_proof_cmds = [human_lemma.replace(human_lemma_name, "humanlemma"), "Proof.",
        "intros.",
        f"rewrite <- {synth_lemma_name}.",
        "reflexivity.",
        "Qed."]
    is_proof_complete_rewrite_left = is_proof_complete(prelude, imports, rewrite_proof_cmds, stmts)
    return is_proof_complete_apply or is_proof_complete_rewrite or is_proof_complete_rewrite_left

def is_version_of_theorem(theorem_name, theorem, lemma, prelude, imports):
    isweaker = is_weaker_than_human(theorem_name, lemma, prelude, imports)
    isstronger = is_stronger_than_human(theorem_name, theorem, lemma, prelude, imports)
    if isweaker and isstronger:
        return True
    else:
        if isweaker:
            return True
    return False


def process_trivial(prelude, imports, lemma):
    lemma = "Lemma " + lemma
    if not is_trivial(lemma, prelude,imports):
        return lemma
    return None

def process_is_version(prelude, imports, theorem_name, theorem, lemma):
    if is_version_of_theorem(theorem_name, theorem, lemma, prelude, imports):
        return None
    return lemma

def process_simplify(prelude, imports, lemma):
    return simplify_lemma(lemma, prelude, imports)

def process(prelude, imports, theorem_name, theorem, lemma):
    lemma = "Lemma " + lemma
    s = None
    if not is_trivial(lemma, prelude,imports) and (not is_version_of_theorem(theorem_name, theorem, lemma, prelude, imports)):
        s = simplify_lemma(lemma, prelude, imports)
    return s

def main():
    args, parser = parse_arguments()
    lemmas = args.lemmas
    imports = args.imports
    prelude = args.prelude
    theorem_name = args.theorem_name
    theorem = args.theorem
    simplified_lemmas = []
    imports = imports
    pool_obj = multiprocessing.Pool(multiprocessing.cpu_count()-1)
    # Filter trivial lemmas
    func_trivial = partial(process_trivial, prelude, imports)
    filtered_trivial = pool_obj.map(func_trivial, lemmas)
    filtered_trivial = [x for x in filtered_trivial if x is not None]
    trivial_count = len(lemmas) - len(filtered_trivial)

    # Filter lemmas is a restatement of the original theorem
    func_isprocess = partial(process_is_version, prelude, imports, theorem_name, theorem)
    filtered_isversion = pool_obj.map(func_isprocess, filtered_trivial)
    filtered_isversion = [x for x in filtered_isversion if x is not None]
    is_version_count = len(filtered_trivial) - len(filtered_isversion)

    #Simplify lemmas
    func_simplify = partial(process_simplify, prelude, imports)
    simplified_lemmas = pool_obj.map(func_simplify, filtered_isversion)

    # func = partial(process, prelude, imports, theorem_name, theorem)
    # simplified_lemmas = pool_obj.map(func, lemmas)
    print("\n")
    print(f"{trivial_count}:trivial_count")
    print(f"{is_version_count}:is_version_count")
    print("start simplified lemmas")
    for l in simplified_lemmas:
        if l != None:
            name = (l[0].split("Lemma ")[1])
            stmt = l[1].replace("\n","")
            print(f"FilteredLemma${name}${stmt}")
    print("end simplified lemmas")


import sys

def trace_calls(frame, event, arg):
    if event != 'call':
        return
    co = frame.f_code
    func_name = co.co_name
    if func_name == 'write':
        # Ignore write() calls from print statements
        return
    func_line_no = frame.f_lineno
    func_filename = co.co_filename
    caller = frame.f_back
    if not caller:
        return
    caller_line_no = caller.f_lineno
    caller_filename = caller.f_code.co_filename
    with open('/home/yousef/mylog', 'a') as f:
        f.write('Call to %s on line %s of %s from line %s of %s' % \
        (func_name, func_line_no, func_filename,
         caller_line_no, caller_filename))
    return
if __name__ == "__main__":
    # sys.settrace(trace_calls)
    main()

import argparse
import os
import csv
from posixpath import dirname, split
from re import S, search, sub
from scipy import stats
import statistics


def parse_arguments():
    parser = argparse.ArgumentParser(
        description=
        "Rank and Generate CSV")
    parser.add_argument('--lfind_op', default="test")
    parser.add_argument('--log_dir', default=".")
    parser.add_argument('--trivial_ld', default=".")
    parser.add_argument('--trivial', default=False)
    return parser.parse_args(), parser


def run(lfind_op):
    time_to_firsts = []
    total_times = []
    total_synth_not_dispro = []
    total_gen_not_dispro = []
    total_gen = []
    total_quickchick = []
    total_proverbot = []
    cat_1 = 0
    total_no_lemmas = 0
    for root, dirs, files in os.walk(lfind_op):
        for name in dirs:
            f_name = os.path.join(root, name)
            if os.path.isdir(f_name) and "_lfind_" in f_name:
                log_summary = os.path.join(f_name, "lfind_summary_log.txt")
                if os.path.exists(log_summary):
                    contents = open(log_summary).readlines()
                else:
                    contents = ""
                time_to_first = 0
                total_time = 0
                gen_not_dispro = 0
                total_no_gen = 0
                total_no_lemmas+=1
                is_cat_1 = False
                for l in contents:
                    if "Time to first category" in l and ":" in l:
                        time_to_first = float(l.split(":")[1].strip())
                    elif "Total Time" in l and ":" in l:
                        total_time = float(l.split(":")[1].strip())
                        if time_to_first == 0:
                            time_to_first = total_time
                        else:
                            print(log_summary)
                            is_cat_1 = True
                            cat_1 += 1
                    elif "#Synthesized Lemmas not disprovable" in l and ":" in l:
                        if is_cat_1:
                            time_to_firsts.append(time_to_first/60.0)
                            total_times.append(time_to_first/60.0)
                        else:
                            total_times.append(total_time/60.0)
                        if int(l.split(":")[1].strip()) !=0:
                            synth = int(l.split(":")[1].strip())
                            total_synth_not_dispro.append(synth)
                            total_gen_not_dispro.append(gen_not_dispro)
                            total_gen.append(total_no_gen)
                            qc = total_no_gen + (total_no_gen-gen_not_dispro)*15
                            provebot = gen_not_dispro * 2 + synth
                            total_quickchick.append(qc)
                            total_proverbot.append(provebot)
                    elif "#Generalizations not disprovable" in l and ":" in l:
                        gen_not_dispro = int(l.split(":")[1].strip())
                    elif "# Generalizations :" in l:
                        total_no_gen = int(l.split(":")[1].strip())


        break
    print("Total #Benchmarks")
    print(total_no_lemmas)
    print("#Category 1 ")
    print(cat_1)
    print("Total Time:")
    print(stats.describe(total_times))
    print(statistics.median(total_times))
    print("Time to Category 1:")
    print(stats.describe(time_to_firsts))
    print(statistics.median(time_to_firsts))
    print("Total Proverbot calls:")
    print(stats.describe(total_proverbot))
    print("Total Quickchick calls:")
    print(stats.describe(total_quickchick))
    print("#Category 1 ")
    print(cat_1)
    print(total_times)
    print(time_to_firsts)
    return 


def main():
    args, parser = parse_arguments()
    run(args.lfind_op)

if __name__ == "__main__":
    main()

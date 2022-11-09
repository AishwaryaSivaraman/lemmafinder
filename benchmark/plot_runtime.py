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
    # lia, clam, compiler
    total_times = [19.683333333333334, 12.716666666666667, 3.0, 18.316666666666666, 13.55, 2.0166666666666666, 65.25, 26.783333333333335, 14.15, 1.1833333333333333, 43.35, 1.9333333333333333, 1.5166666666666666, 2.7666666666666666, 1.4166666666666667, 12.766666666666667, 23.466666666666665, 1.3166666666666667, 35.3, 8.583333333333334, 9.9, 71.46666666666667, 1.05, 8.4, 0.9, 0.4666666666666667, 3.3, 12.583333333333334, 3.8333333333333335, 4.683333333333334, 13.283333333333333, 1.35, 0.45, 4.616666666666666, 22.433333333333334, 1.3666666666666667, 0.85, 14.433333333333334, 11.55, 1.6833333333333333, 9.633333333333333, 66.58333333333333, 47.36666666666667, 3.6, 0.65, 1.0666666666666667, 1.1166666666666667, 11.75, 4.316666666666666, 18.233333333333334, 1.2666666666666666, 6.366666666666666, 22.6, 1.7, 47.46666666666667, 2.95, 1.5666666666666667, 1.3, 1.5666666666666667, 0.65, 14.583333333333334, 4.3, 5.366666666666666, 0.6166666666666667, 0.6333333333333333, 4.683333333333334, 0.65, 12.033333333333333, 3.6, 1.3166666666666667, 0.4666666666666667, 0.95, 0.9166666666666666, 53.35, 10.416666666666666, 15.1, 1.0, 1.1833333333333333, 0.48333333333333334, 0.6833333333333333, 3.45, 14.55, 0.6666666666666666, 1.6666666666666667, 0.3333333333333333, 7.3, 16.233333333333334, 2.5833333333333335, 0.6666666666666666, 0.9666666666666667, 29.416666666666668, 31.666666666666668, 6.516666666666667, 3.433333333333333, 8.95, 2.2666666666666666, 1.25, 0.6, 1.5, 1.1, 0.35, 17.05, 0.9333333333333333, 15.516666666666667, 46.083333333333336, 11.5, 1.4, 1.1666666666666667, 1.0666666666666667, 8.833333333333334, 24.8, 0.48333333333333334, 0.8333333333333334, 8.6, 26.883333333333333, 32.95, 0.75, 6.5, 0.6833333333333333, 0.65, 3.6166666666666667, 4.8, 7.183333333333334, 10.566666666666666, 1.1833333333333333, 11.383333333333333, 21.633333333333333, 39.733333333333334, 0.7833333333333333, 1.2333333333333334, 12.55, 33.3, 2.283333333333333, 0.6, 5.783333333333333, 4.433333333333334, 1.6, 0.8, 0.9, 1.3833333333333333, 1.6333333333333333, 10.566666666666666, 3.85, 15.883333333333333, 1.4, 3.7666666666666666, 0.9333333333333333, 1.2333333333333334, 5.15, 36.88333333333333, 0.36666666666666664, 4.85, 3.966666666666667, 1.4833333333333334, 0.5333333333333333, 1.25, 4.133333333333334, 1.5166666666666666, 19.55, 7.85, 1.5666666666666667, 4.666666666666667, 18.933333333333334, 1.6333333333333333, 1.95, 1.2833333333333334, 0.43333333333333335, 11.75, 16.95, 0.6166666666666667, 4.616666666666666, 10.95, 1.0166666666666666, 10.966666666666667, 3.3833333333333333, 0.6833333333333333, 106.83333333333333, 1.4, 14.383333333333333, 20.533333333333335, 0.45, 7.0, 1.1833333333333333, 0.5166666666666667, 48.18333333333333, 3.0166666666666666, 10.516666666666667, 2.566666666666667, 0.5833333333333334, 4.35, 1.2833333333333334, 42.13333333333333, 19.6, 7.25, 3.6166666666666667, 8.95, 0.7333333333333333, 1.3666666666666667, 1.35, 11.15, 35.416666666666664, 104.69]
    time_to_firsts = [3.0, 2.0166666666666666, 1.1833333333333333, 1.9333333333333333, 1.5166666666666666, 2.7666666666666666, 1.4166666666666667, 1.05, 0.9, 4.683333333333334, 13.283333333333333, 1.35, 0.45, 0.85, 11.55, 0.65, 1.1166666666666667, 2.95, 1.3, 1.5666666666666667, 0.65, 14.583333333333334, 4.3, 0.6166666666666667, 0.6333333333333333, 0.65, 3.6, 1.3166666666666667, 0.4666666666666667, 1.0, 0.48333333333333334, 0.6833333333333333, 3.45, 0.3333333333333333, 7.3, 0.6666666666666666, 0.9666666666666667, 3.433333333333333, 8.95, 2.2666666666666666, 1.25, 0.6, 1.5, 0.35, 1.0666666666666667, 0.48333333333333334, 0.6833333333333333, 0.65, 0.7833333333333333, 1.2333333333333334, 0.6, 5.783333333333333, 4.433333333333334, 0.9, 1.3833333333333333, 1.4, 1.2333333333333334, 0.36666666666666664, 1.4833333333333334, 0.5333333333333333, 4.133333333333334, 19.55, 7.85, 1.5666666666666667, 0.43333333333333335, 0.6166666666666667, 1.0166666666666666, 3.3833333333333333, 0.6833333333333333, 1.4, 0.45, 7.0, 0.5166666666666667, 3.0166666666666666, 2.566666666666667, 4.35, 3.6166666666666667, 0.7333333333333333, 1.35]
    # total_times = []
    # time_to_firsts = []
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

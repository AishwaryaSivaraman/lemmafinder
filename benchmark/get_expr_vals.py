import re
import argparse

def parse_arguments():
    parser = argparse.ArgumentParser(
        description=
        "Prase Coq output of lfind_eval.v")
    parser.add_argument('--input', type=str, required=True)
    return parser.parse_args()

def main():
  args = parse_arguments()
  result = re.findall('^[ ]*= (?P<value>(?:.(?!^[ ]*:))+)\n^[ ]*: (?P<type>[\w (->)]+)(?:\n|\Z)', args.input, re.MULTILINE|re.DOTALL)
  print(result)

if __name__ == "__main__":
  main()

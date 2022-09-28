#!/usr/bin/env python3
# ----------------------------------
import sys
import getopt

from fofspec import FOFSpec
from version import version
from alternating_path import AlternatingPath

max_depth = float('inf')


def processOptions(opts):
    """
    Process the options given
    """
    global max_depth
    for opt, optarg in opts:
        if opt == "-h" or opt == "--help":
            print("pyres-simple.py " + version)
            print(__doc__)
            sys.exit()
        elif opt == "-m" or opt == "--max-depth":
            max_depth = int(optarg)


if __name__ == '__main__':
    try:
        opts, args = getopt.gnu_getopt(sys.argv[1:],
                                       "hm:S",
                                       ["help", "max-depth", "supress-eq-axioms"])
    except getopt.GetoptError as err:
        print(sys.argv[0], ":", err)
        sys.exit(1)

    processOptions(opts)

    problem = FOFSpec()
    for file in args:
        problem.parse(file)
    # problem.addEqAxioms()
    cnf = problem.clausify()

    ap = AlternatingPath(cnf, limit=max_depth)
    selection = ap.select_clauses()
    print(selection)

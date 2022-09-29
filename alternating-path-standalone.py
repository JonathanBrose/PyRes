#!/usr/bin/env python3
# ----------------------------------
import sys
import getopt
from resource import getrusage, RUSAGE_SELF

from fofspec import FOFSpec
from version import version
from alternating_path import AlternatingPath

max_depth = float('inf')
verbose = False


def process_options(opts):
    """
    Process the options given
    """
    global max_depth, verbose
    for opt, optarg in opts:
        if opt == "-h" or opt == "--help":
            print("pyres-simple.py " + version)
            print(__doc__)
            sys.exit()
        elif opt == "-l" or opt == "--limit":
            max_depth = int(optarg)
        elif opt == "-v" or opt == "--verbose":
            verbose = True


if __name__ == '__main__':
    try:
        opts, args = getopt.gnu_getopt(sys.argv[1:],
                                       "hl:v",
                                       ["help", "limit", "verbose"])
    except getopt.GetoptError as err:
        print(sys.argv[0], ":", err)
        sys.exit(1)

    process_options(opts)

    problem = FOFSpec()
    for file in args:
        problem.parse(file)
    problem.addEqAxioms()
    cnf = problem.clausify()

    ap = AlternatingPath(cnf, limit=max_depth, verbose=verbose)
    selection = ap.select_clauses()

    print("-----------------------------")
    print(selection)
    if verbose:
        print()
        print("------- Statistics -----------")
        print(ap.statistics_str())

        resources = getrusage(RUSAGE_SELF)
        print("# -------- CPU Time ---------")
        print("# User time          : %.3f s" % (resources.ru_utime,))
        print("# System time        : %.3f s" % (resources.ru_stime,))
        print("# Total time         : %.3f s" % (resources.ru_utime +
                                                 resources.ru_stime,))
        print("------------------------------")

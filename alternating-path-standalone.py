#!/usr/bin/env python3
# ----------------------------------
import sys
import getopt
from resource import getrusage, RUSAGE_SELF

from clausesets import ClauseSet
from fofspec import FOFSpec
from version import version
from alternating_path_selection import AlternatingPathSelection
from simple_path_selection import SimplePathSelection
from resource import RLIMIT_STACK, setrlimit, getrlimit
from signal import  signal, SIGXCPU

limit = None
stats = False
no_output = False
indexed = False
include_equality = True
dumb = False


def process_options(opts):
    """
    Process the options given
    """
    global limit, no_output, stats, indexed, include_equality, dumb
    for opt, optarg in opts:
        if opt == "-h" or opt == "--help":
            print("alternating-path-standalone.py "+version)
            print(__doc__)
            sys.exit()
        elif opt == "-l" or opt == "--limit":
            limit = int(optarg)
        elif opt == "-s" or opt == "--stats":
            stats = True
        elif opt == "-n" or opt == "--no-output":
            no_output = True
        elif opt == "-i" or opt == "--indexed":
            indexed = True
        elif opt == "-e" or opt == "--exclude-equality":
            include_equality = False
        elif opt == "-d" or opt == "--dumb":
            dumb = True
        elif opt == "--no-stacktrace":
            sys.tracebacklimit = 0


def timeout_handler(sign, frame):
    """
    This will be called if the process receives a SIGXCPU error. In
    that case, we print an informative message before terminating. We
    expect this signal from the benchmark environment (typically
    StarExec).
    """
    print("# Failure: Resource limit exceeded (time)")
    print("# SZS status ResourceOut")
    sys.exit(0)


if __name__ == '__main__':
    try:
        soft, hard = getrlimit(RLIMIT_STACK)
        soft = 10*soft
        if 0 < hard < soft:
            soft = hard
        setrlimit(RLIMIT_STACK, (soft, hard))
    except ValueError:
        # For reasons nobody understands, this seems to fail on
        # OS-X. In that case, we just do our best...
        pass

    signal(SIGXCPU, timeout_handler)
    sys.setrecursionlimit(10000)

    try:
        opts, args = getopt.gnu_getopt(sys.argv[1:],
                                       "hl:nsied",
                                       ["help",
                                        "no-stacktrace",
                                        "limit=",
                                        "no-output",
                                        "stats",
                                        "indexed",
                                        "exclude-equality",
                                        "dumb"])
    except getopt.GetoptError as err:
        print(sys.argv[0], ":", err)
        sys.exit(1)

    process_options(opts)

    problem = FOFSpec()
    for file in args:
        problem.parse(file)
    normal_clauses = [c for c in problem.clauses]
    problem.addEqAxioms()
    equality_clauses = [c for c in problem.clauses if c not in normal_clauses]
    cnf = problem.clausify()

    if not include_equality:
        for c in equality_clauses:
            cnf.extractClause(c)

    ap = AlternatingPathSelection(cnf.clauses, limit, indexed=indexed, equality_clauses=equality_clauses) if not dumb \
        else SimplePathSelection(cnf.clauses, limit, indexed=indexed, equality_clauses=equality_clauses)

    selection = ClauseSet(ap.select_clauses())

    if not include_equality:
        for c in equality_clauses:
            selection.addClause(c)

    if not no_output:
        print("-----------------------------")
        print(selection)
        print()
    if stats:
        print("------- Statistics -----------")
        print(ap.statistics_str())
        if equality_clauses:
            print(f"# Equality clauses   : {len(equality_clauses)} ({'incl.' if include_equality else 'excl.'})")
        resources = getrusage(RUSAGE_SELF)
        print("# -------- CPU Time ---------")
        print("# User time          : %.3f s" % (resources.ru_utime,))
        print("# System time        : %.3f s" % (resources.ru_stime,))
        print("# Total time         : %.3f s" % (resources.ru_utime +
                                                 resources.ru_stime,))
        print("------------------------------")
        print()

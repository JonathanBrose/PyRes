import sys
import getopt

from fofspec import FOFSpec
from version import version
from lexer import Token, Lexer
from clausesets import ClauseSet
from alternating_path2 import AlternatingPath

max_depth = float('inf')


def processOptions(opts):
    """
    Process the options given
    """
    global max_depth, suppressEqAxioms
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

    cnf = problem.clausify()
    # problem = ClauseSet()
    #
    # for file in args:
    #     fp = open(file, "r")
    #     input = fp.read()
    #     fp.close()
    #     lex = Lexer(input)
    #     problem.parse(lex)

    ap = AlternatingPath(cnf, limit=max_depth)
    selection = ap.saturate()
    print(selection)

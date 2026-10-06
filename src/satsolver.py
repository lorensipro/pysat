import time, sys

# My imports
from satutils import *
from sattypes import intToLit, litToInt, notLit, litToVar, varToLit, signLit # (not the old Clause class of sattypes)
from satstats import *

class Clause(list):
    ''' A clause is simply a list of (internal) literals: c[i] and len(c) are as fast as possible.
        Each solver can add its own attributes to the clauses (counters, scores, ...)'''
    def __init__(self, literals, learnt = False):
        list.__init__(self, literals)
        self.learnt = learnt
    __hash__ = object.__hash__        # Two clauses are equal only if they are the same object
    def __eq__(self, other):
        return self is other
    def __str__(self):
        return " ".join(str(litToInt(l)) for l in self)


class Solver():
    ''' The root of all the solvers (complete or not). It only knows the formula as given by
        the user, the API and the statistics. Some function names are taken from the Minisat interface.

        A solver built on it has to give:
            _newVar()          a new variable is created: grow all the per-variable data structures
            _addClause(lits)   a new clause is added (internal literals, no duplicate, no tautology)
            _solve()           the search itself: returns lit_True, lit_False or lit_Undef,
                               and fills self.finalModel when it returns lit_True
    '''

    class Constants():
        '''Constants used inside the solver and outside, to read the search status'''
        lit_False = 0
        lit_True = 1
        lit_Undef = 2

    class Configuration():
        ''' Contains all the configuration variables for the solver '''
        verbosity = 1
        printModel = True

    def __init__(self):
        self._cst = self.Constants()
        self._config = self.Configuration() # Configuration of this solver

        self._nbvars = 0               # Number of variables (created on the fly by addClause)
        self._originalClauses = []     # The clauses as given by the user (used to check the models)
        self._ok = True                # False when the formula is known to be UNSAT (empty clause found)
        self.finalModel = []           # the model (if SAT) will be copied in this array of variables

        self._stats = Stats()          # statistics (see satstats.py): each solver adds its own counters
        return

    def addClause(self, listOfInts):
        ''' API function to add a clause (a list of non zero ints, as in DIMACS). Clauses can be
            added before the first call to solve(), or between two calls (incremental SAT).
            The variables are created on the fly.'''
        self._originalClauses.append(list(listOfInts))
        lits = []
        for i in listOfInts:
            if -i in lits: return                                  # Tautology: the clause is always satisfied, we skip it
            if i not in lits: lits.append(i)                       # Duplicated literals are removed
        for i in lits:
            while abs(i) > self._nbvars: self._newVar()            # Creates the missing variables
        if self._ok: self._addClause([intToLit(i) for i in lits])

    def _newVar(self):
        ''' A new variable is created. Each solver adds its own data structures (calling this one first)'''
        self._nbvars += 1

    def _addClause(self, lits):
        raise NotImplementedError

    def _solve(self):
        raise NotImplementedError

    def solve(self):
        ''' Returns lit_True (SAT, the model is in finalModel), lit_False (UNSAT) or lit_Undef
            (unknown: incomplete solver, or interrupted by the user. In this last case, the
            solver should not be used anymore).'''
        self.finalModel = []
        if not self._ok: return self._cst.lit_False                # The empty clause was already found
        self._stats.startSearch()
        try:
            status = self._solve()
        except KeyboardInterrupt:
            print("c Interrupted")
            status = self._cst.lit_Undef
        self._stats.stopSearch()

        if status == self._cst.lit_True:
            assert self._checkModel(self.finalModel), "The model does not satisfy the formula"
        elif status == self._cst.lit_False:
            self._ok = False                                       # Adding clauses will not change it
        return status

    def _checkModel(self, model):
        ''' Checks that the model satisfies all the clauses given by the user '''
        trueLits = set(model)
        return all(any(l in trueLits for l in c) for c in self._originalClauses)

    def printFinalStats(self):
        self._stats.printFinal()


def banner(title):
    _thisispysat = r'''
   ___         ____ ___  ______
  / _ \ __ __ / __// _ |/_  __/
 / ___// // /_\ \ / __ | / /
/_/    \_, //___//_/ |_|/_/
      /___/
'''
    print('\n'.join([ 'c \033[1;31m' + line + '\033[0m' for line in _thisispysat.split('\n')]))
    print("c                               \033[1;33mThis is pysat ({t:s}) (L. Simon 2016-2026)\033[0m\nc".format(t=title))


def runFromCommandLine(solverClass, title):
    ''' The main program of all the solvers, as in the SAT competitions:
        1- Print the banner
        2- Read the CNF and push all the clauses to a new solver
        3- Solve it
        4- Print the result, the statistics, the model and exit with the correct error code'''
    banner(title)
    if len(sys.argv) < 2:
        print("c - Error - Please give me a cnf(.gz) file as input")
        sys.exit(1)

    solver = solverClass()
    readFile(solver, sys.argv[1], solver._config.verbosity)
    if solver._config.verbosity > 0:
        print("c Ready to go with {v:d} variables and {c:d} clauses".format(v=solver._nbvars, c=len(solver._originalClauses)))

    result = solver.solve()

    if result == solver._cst.lit_False:
        print("s UNSATISFIABLE")
    elif result == solver._cst.lit_True:
        print("s SATISFIABLE")
    else:
        print("s UNKNOWN")
    solver.printFinalStats()

    if result == solver._cst.lit_True and solver._config.printModel: # SAT was claimed
        print("v " + " ".join(str(v) for v in solver.finalModel) + " 0")

    if result == solver._cst.lit_False:
       sys.exit(20)
    if result == solver._cst.lit_True:
       sys.exit(10)

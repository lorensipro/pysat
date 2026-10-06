from array import *
import time, sys

# My imports
from satutils import *
from sattypes import *
from satheapq import *
from prettyPrinter import *

class Solver():
    ''' A plain DPLL solver (no learning, chronological backtracking), written as
        close as possible to the CDCL solver of pysat.py to compare both algorithms.
        Some function names are taken from the Minisat interface '''

    class Constants():
        '''Constants used inside the solver and outside, to read the search status'''
        lit_False = 0
        lit_True = 1
        lit_Undef = 2

    class Configuration():
        ''' Contains all the configuration variables for the solver '''
        default_value = False     # default value for branching
        verbosity = 1
        printModel = True

    def __init__(self):
        self._cst = self.Constants()
        self._config = self.Configuration() # Configuration of this solver

        self._nbvars = 0               # Number of variables
        self._scores = MyArray('d')    # Array of doubles, (static) score of each variable: its number of occurrences
        self._clauses = []             # Simply the list of initial clauses
        self._reason = MyList()        # self._reason[v] is the clause that propagated the literal v or -v (or None if v,-v was a decision)
        self._occ = MyList()           # self._occ[l] is the list of clauses in which the literal l occurs
        self._values = MyArray('b')    # Current assigned values for each variable (in Constants())
        self._level = MyArray('I')     # decision level of this assigned variable

        self.finalModel = []          # the model (if SAT) will be copied in this array of variables)
        self._trivialUnsat = False    # True if the empty clause (or two opposite unary clauses) were found in the input

        self._time0 = time.time()
        self._varHeap = SatHeapq(lambda x,y: self._scores[x] > self._scores[y]) # Heap of variables (the most frequent first)

        # statistics
        self._conflicts = 0          # total number of conflicts
        self._decisions = 0          # total number of decisions
        self._propagations = 0       # total number of propagations
        self._occInspections = 0     # number of inspected clauses during propagations
        self._sumDecisionLevel = 0

        # Propagation Queue
        self._trail = MyList()          # trail representing the current partial assignment (trail of literals)
        self._trailLevels = MyList()    # Splits the trail in levels
        self._trailIndexToPropagate = 0 # Handles the propagation queue. Literals in _trail (strictly) above are already propagated

        return

    def _valueLit(self, l):
        ''' Returns the value of the lit according to the current partial assignment '''
        v,s = litToVarSign(l)
        if self._values[v] == self._cst.lit_Undef: return self._cst.lit_Undef
        if s:
            return self._cst.lit_False if self._values[v] == self._cst.lit_True  else self._cst.lit_True
        return self._values[v]

    def _pickBranchLit(self):
        ''' Returns the literal on which we must branch. None if no more
        literals are unassigned. The scores are static (TODO: dynamic heuristics
        like MOMS or Jeroslow-Wang, based on the size of the non satisfied clauses)'''
        v = None
        while len(self._varHeap) > 0:
            v = self._varHeap.removeMin()
            if self._values[v] == self._cst.lit_Undef: break
        if v == None or self._values[v] != self._cst.lit_Undef: return None
        return varToLit(v, 0 if self._config.default_value else 1)

    def _cancelUntil(self, level = 0):
        ''' Backtrack to the given level (undoing everything).'''

        if len(self._trailLevels) <= level:
          return

        for x in range(len(self._trail) - 1, self._trailLevels[level] - 1, -1):
            v = litToVar(self._trail[x])
            self._values[v] = self._cst.lit_Undef # Simply unassign each variable
            if not self._varHeap.inHeap(v):
                self._varHeap.insert(v)           # Put back the variable into the heap (if not already in it)

        del self._trail[self._trailLevels[level] - len(self._trail):] # shrinks the trail
        self._trailIndexToPropagate = self._trailLevels[level]
        del self._trailLevels[level - len(self._trailLevels):]        # shrinks the traillevels

    def _newDecisionLevel(self):
        ''' Adds a new decision level. Any new literal pushed on the trail will be at this decision level '''
        self._trailLevels.append(len(self._trail))

    def _decisionLevel(self):
        ''' The decision level is simply the size of this vector '''
        return len(self._trailLevels)

    def _uncheckedEnqueue(self, l, r=None):
        ''' Enqueue a literal l to the propagation queue.
            This is unchecked in the sense that no contradiction can be detected'''
        v,s = litToVarSign(l)
        assert self._values[v] == self._cst.lit_Undef # Checks that the literal was not already assigned
        self._values[v] = self._cst.lit_False if s else self._cst.lit_True
        self._reason[v] = r
        self._level[v] = self._decisionLevel()
        self._trail.append(l)

    def _propagate(self):
        ''' Can return a conflict or None
            This version simply visits all the clauses in which the opposite literal occurs'''
        while self._trailIndexToPropagate < len(self._trail):
            self._propagations += 1
            litToPropagate = self._trail[self._trailIndexToPropagate]
            self._trailIndexToPropagate += 1

            for c in self._occ[notLit(litToPropagate)]:              # c is a clause containing -litToPropagate (now false)
                self._occInspections += 1
                nbUndef = 0; lastUndef = None; satisfied = False
                for l in c:
                    val = self._valueLit(l)
                    if val == self._cst.lit_True:                    # The clause is satisfied, nothing to do
                        satisfied = True
                        break
                    if val == self._cst.lit_Undef:
                        nbUndef += 1; lastUndef = l
                if satisfied: continue
                if nbUndef == 0:                                     # The clause is empty
                    self._trailIndexToPropagate = len(self._trail)   # No more literal to propagate
                    return c                                         # the empty clause to return
                if nbUndef == 1:                                     # The clause is unary (and lastUndef is forced)
                    self._uncheckedEnqueue(lastUndef, c)
        return None

    def addClause(self, listOfInts):
        ''' API function to add a clause to the solver. Right now, the function
        buildDataStructure must be called once after all the clauses have been
        added to the solver.'''
        lits = []
        for i in listOfInts:
            if -i in lits: return                                  # Tautology: the clause is always satisfied, we skip it
            if i not in lits: lits.append(i)                       # Duplicated literals are removed
        self._clauses.append(Clause([intToLit(l) for l in lits]))
        self._nbvars = max([self._nbvars] + [abs(i) for i in lits])

    def buildDataStructure(self):
        ''' Takes all the clauses sent to the solver via the addClause function and
        effectively add them to the data structure used by the solver. This function
        must be called only once for each run.'''
        starttime = time.time()

        self._values.growTo(self._nbvars, self._cst.lit_Undef)
        for e in [self._scores, self._reason, self._level]:
            e.growTo(self._nbvars)
        self._occ.growTo(self._nbvars * 2, [])

        for c in self._clauses:
            if len(c)==0:                                          # The empty clause: the formula is trivially UNSAT
                self._trivialUnsat = True
            elif len(c)==1:                                        # Special case for unary clauses : literal is directly enqueued at decision level 0
                if self._valueLit(c[0]) == self._cst.lit_False:    # The opposite unary clause was already enqueued
                    self._trivialUnsat = True
                elif self._valueLit(c[0]) == self._cst.lit_Undef:  # (if the literal is already true, nothing to do)
                    self._uncheckedEnqueue(c[0])
            for l in c:
                self._occ[l].append(c)
                self._scores[litToVar(l)] += 1                     # each occurrence counts as 1

        for i in range(0,self._nbvars): self._varHeap.insert(i)     # push all the variables on the heap

        if self._config.verbosity > 0:
           print("c Building data structures in {t:03.2f}s".format(t=time.time()-starttime))
           print("c Ready to go with {v:d} variables and {c:d} clauses".format(v=self._nbvars,
                  c=len(self._clauses)))

    def _printState(self):
        printTrail(self)
        printClauses(self, assigned = lambda x: self._valueLit(x)!=self._cst.lit_Undef, value=lambda x:self._valueLit(x)==self._cst.lit_True)

    # Simply print the search progress
    def _reportSearch(self):
      print("c {cfl:d} conflicts, {dec:d} decisions, {prop:d} propagations, {depth:d} decisions depth".format(cfl=self._conflicts,
        dec=self._decisions,
        prop=self._propagations,
        depth = int(self._sumDecisionLevel / (1 if self._conflicts == 0 else self._conflicts))))

    # The main DPLL search procedure
    def _search(self):
        while True:
            confl = self._propagate()
            if confl is not None:                                         # We reached a conflict
                self._conflicts += 1
                self._sumDecisionLevel += self._decisionLevel()           # stats about the search

                if self._conflicts % 1000 == 0 and self._config.verbosity > 0:
                    self._reportSearch()                                  # reports the search status every 1000 conflicts

                if self._decisionLevel() == 0: return self._cst.lit_False # We proved UNSAT

                lastDecision = self._trail[self._trailLevels[-1]]         # The decision of the current level
                self._cancelUntil(self._decisionLevel() - 1)              # Chronological backtracking
                self._uncheckedEnqueue(notLit(lastDecision))              # Flips it: now implied at the previous level, it will be
                                                                          # undone when the decision of this level is flipped
            else:                                                          # No conflict
                l = self._pickBranchLit()                                  # Picks a new variable to branch on
                if l == None: return self._cst.lit_True                    # All variables are assigned and no conflict: SAT was proven
                self._decisions += 1
                self._newDecisionLevel()                                   # Creates a new decision level
                self._uncheckedEnqueue(l)                                  # propagates this literal with no reason (this is a decision)

    def solve(self):
        '''Calls the search function. This function can return lit_Undef
           if interrupted by the user.'''
        self._time1 = time.time()
        if self._trivialUnsat:                                     # Nothing to search: the formula contains the empty clause
            self._searchTime = time.time() - self._time1
            return self._cst.lit_False
        try:
            self._status = self._search()
        except KeyboardInterrupt:
            self._searchTime = time.time() - self._time1
            print("c Interrupted")
            self.printFinalStats()
            return self._cst.lit_Undef   # Interrupted

        self._searchTime = time.time() - self._time1

        if self._status == self._cst.lit_True: # We copy the solution before cancelling the decisions
          assert len(self.finalModel)==0
          for v, val in enumerate(self._values):
              assert val != self._cst.lit_Undef
              self.finalModel.append(v+1 if val==self._cst.lit_True else -v-1) # API: users can read the values in this array

        self._cancelUntil(0)
        return self._status

    def printFinalStats(self):
        if self._conflicts == 0:
            print("c conflicts: 0")
            return
        print("c cpu time: \033[1;32m{t:03.2f}\033[0ms (search={ts:03.2f}s)".format(t=time.time()-self._time0, ts=self._searchTime))
        print("c conflicts:", self._conflicts, "(" + str(int(self._conflicts /max(self._searchTime, 1e-6))) + "/s)")
        print("c decisions:", self._decisions)
        print("c propagations:", self._propagations, "(" + str(int(self._propagations / max(self._searchTime, 1e-6))) + "/s)")
        print("c Inspected clauses:", self._occInspections)
        print("c Avg Decision Levels: " + str(int(self._sumDecisionLevel / self._conflicts)))


# when running as a solver:
# 1- Print the banner
# 2- Read the CNF
# 3- Push all the clauses to a new solver
# 4- Solve it
# 5- Interpret the result

if __name__ == "__main__":

    def printUsage():
       print("c pysat solver: learning clause learning algorithms (slowly learning things). DPLL version.")

    def banner():
        _thisispysat = r'''
   ___         ____ ___  ______
  / _ \ __ __ / __// _ |/_  __/
 / ___// // /_\ \ / __ | / /
/_/    \_, //___//_/ |_|/_/    (DPLL)
      /___/
'''
        print('\n'.join([ 'c \033[1;31m' + line + '\033[0m' for line in _thisispysat.split('\n')]))
        print("c                               \033[1;33mThis is pysat DPLL 0.2 (L. Simon 2016-2026)\033[0m\nc")
        print("c A plain DPLL (no learning, chronological backtracking), to compare with pysat.py (CDCL)")

    banner()
    solver = Solver()

    if len(sys.argv) > 1:
        readFile(solver, sys.argv[1])
        solver.buildDataStructure()
    else:
        printUsage()
        print("c - Error - Please give me a cnf(.gz) file as input")
        sys.exit(1)

    result = solver.solve()

    if result == solver._cst.lit_False:
        print("s UNSATISFIABLE")
    elif result == solver._cst.lit_True:
        print("s SATISFIABLE")
    else:
        print("s UNKNOWN")
    solver.printFinalStats()

    if result == solver._cst.lit_True and solver._config.printModel: # SAT was claimed
        print("v ", end="")
        for v in solver.finalModel:
             print(v," ", end="")
        print("0")

    # As in the SAT competition, ends with the correct error code
    if result == solver._cst.lit_False:
       sys.exit(20)
    if result == solver._cst.lit_True:
       sys.exit(10)

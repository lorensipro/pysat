from satsolver import *

class DPLL(Solver):
    ''' The DPLL algorithm (Davis, Logemann, Loveland 1962): unit propagation, decisions and
        chronological backtracking. No learning.

        It is written as a CDCL solver that would learn, at each conflict, the "decision clause"
        (the negation of all the current decisions) and would forget it right after: this clause
        is only the reason of the flipped decision. The CDCL solvers will just learn better clauses
        (by redefining _analyze and _learn).

        The unit propagation uses counters: each clause knows how many of its literals were
        propagated true and false. They must be restored when backtracking (see _unpropagateLit).'''

    class Configuration(Solver.Configuration):
        ''' Contains all the configuration variables for the solver '''
        default_value = False          # default value for branching

    def __init__(self):
        super().__init__()

        self._clauses = []             # The clauses of the formula (simplified at level 0)
        self._occ = []                 # self._occ[l] is the list of the clauses in which the literal l occurs
        self._litValues = []           # self._litValues[l] is the value of the literal l (in Constants())
        self._level = []               # self._level[v] is the decision level of the assigned variable v
        self._reason = []              # self._reason[v] is the clause that propagated v or -v (None for a decision)
        self._order = []               # The variables, in the order they are picked for decisions (computed by _solve)

        # Propagation Queue
        self._trail = []                # trail representing the current partial assignment (trail of literals)
        self._trailLevels = []          # self._trailLevels[i] is the index in the trail of the decision of level i+1
        self._trailIndexToPropagate = 0 # Handles the propagation queue. Literals in _trail (strictly) above are already propagated

        self._stats.addCounter('conflicts', "conflicts", rate='time')
        self._stats.addCounter('decisions', "decisions", rate='time')
        self._stats.addCounter('propagations', "propagations", rate='time')
        self._stats.addCounter('clauseUpdates', "Clause counters updated", rate='propagations')
        self._stats.addCounter('clauseRestores', "Clause counters restored", rate='propagations')
        self._stats.addCounter('sumDecisionLevel')                         # sum of the decision levels of the conflicts
        self._stats.addAverage("Avg Decision Levels", 'sumDecisionLevel', 'conflicts')
        return

    def _newVar(self):
        ''' A new variable: its two literals are not assigned and occur in no clause '''
        super()._newVar()
        self._litValues += [self._cst.lit_Undef, self._cst.lit_Undef]
        self._occ += [[], []]
        self._level.append(0)
        self._reason.append(None)

    def _addClause(self, lits):
        ''' Adds a clause at decision level 0, simplified by the literals already assigned '''
        assert self._decisionLevel() == 0
        for l in lits:
            if self._litValues[l] == self._cst.lit_True: return    # The clause is already satisfied at level 0
        lits = [l for l in lits if self._litValues[l] != self._cst.lit_False] # The false literals are useless
        if len(lits) == 0:                                         # The empty clause: the formula is UNSAT
            self._ok = False
            return
        c = Clause(lits)
        self._clauses.append(c)
        self._attachClause(c)
        if len(lits) == 1:                                         # A unary clause: its literal is propagated right now
            self._uncheckedEnqueue(lits[0], c)
            if self._propagate() is not None: self._ok = False

    def _attachClause(self, c):
        ''' The clause becomes visible for the propagation. It must be called when all the
            literals of the trail are propagated (at level 0, or just after a backtrack): the
            counters can then be computed from the current values of the literals '''
        assert self._trailIndexToPropagate == len(self._trail)
        c.nbTrue = 0                                               # Number of its literals that were propagated true
        c.nbFalse = 0                                              # ... and false
        for l in c:
            self._occ[l].append(c)
            if self._litValues[l] == self._cst.lit_True: c.nbTrue += 1
            elif self._litValues[l] == self._cst.lit_False: c.nbFalse += 1

    def _decisionLevel(self):
        ''' The decision level is simply the size of this vector '''
        return len(self._trailLevels)

    def _newDecisionLevel(self):
        ''' Adds a new decision level. Any new literal pushed on the trail will be at this decision level '''
        self._trailLevels.append(len(self._trail))

    def _uncheckedEnqueue(self, l, r=None):
        ''' Assigns the literal l to true and enqueues it to the propagation queue.
            This is unchecked in the sense that no contradiction can be detected'''
        assert self._litValues[l] == self._cst.lit_Undef           # Checks that the literal was not already assigned
        self._litValues[l] = self._cst.lit_True
        self._litValues[notLit(l)] = self._cst.lit_False
        v = litToVar(l)
        self._level[v] = self._decisionLevel()
        self._reason[v] = r
        self._trail.append(l)

    def _propagate(self):
        ''' Propagates all the literals of the queue. Returns a conflict (a clause whose literals
            are all false) or None'''
        stats = self._stats                                        # local variable: faster in the loop
        while self._trailIndexToPropagate < len(self._trail):
            l = self._trail[self._trailIndexToPropagate]
            self._trailIndexToPropagate += 1                       # l will be entirely propagated, even if there is a conflict
            stats.propagations += 1
            confl = self._propagateLit(l)
            if confl is not None: return confl
        return None

    def _propagateLit(self, l):
        ''' The literal l (already true) is propagated: the counters of its clauses are updated, and
            the clauses that become unit force their last literal. Returns a conflict or None.
            Even when a conflict is found, all the counters are updated: the backtrack can then
            undo exactly what was done for each propagated literal.'''
        litValues = self._litValues                                # local variable: faster in the loop
        conflict = None
        for c in self._occ[l]:                                     # These clauses are satisfied by l
            c.nbTrue += 1
        for c in self._occ[notLit(l)]:                             # These clauses have one more false literal
            c.nbFalse += 1
            if conflict is not None or c.nbTrue > 0: continue      # (already satisfied: nothing to do)
            if c.nbFalse == len(c):                                # All its literals are false: a conflict
                conflict = c
            elif c.nbFalse == len(c) - 1:                          # Only one literal is not (yet) propagated false
                for x in c:
                    if litValues[x] != self._cst.lit_False:
                        if litValues[x] == self._cst.lit_Undef:    # The clause is unit: x is forced
                            self._uncheckedEnqueue(x, c)
                        break                                      # (if x is true, the clause is satisfied)
                                                                   # (if all are false, a literal is still in the queue:
                                                                   #  the conflict will be found when it is propagated)
        self._stats.clauseUpdates += len(self._occ[l]) + len(self._occ[notLit(l)])
        return conflict

    def _unpropagateLit(self, l):
        ''' Restores the counters as they were before the propagation of l '''
        for c in self._occ[l]: c.nbTrue -= 1
        for c in self._occ[notLit(l)]: c.nbFalse -= 1
        self._stats.clauseRestores += len(self._occ[l]) + len(self._occ[notLit(l)])

    def _cancelUntil(self, level = 0):
        ''' Backtrack to the given level (undoing everything above it). '''
        if self._decisionLevel() <= level:
          return
        start = self._trailLevels[level]                           # Index in the trail of the first literal to undo
        for x in range(self._trailIndexToPropagate - 1, start - 1, -1):
            self._unpropagateLit(self._trail[x])                   # Only the propagated literals touched the counters
        for x in range(len(self._trail) - 1, start - 1, -1):
            l = self._trail[x]
            self._litValues[l] = self._litValues[notLit(l)] = self._cst.lit_Undef # Simply unassign each variable
        del self._trail[start:]                                    # shrinks the trail
        del self._trailLevels[level:]                              # shrinks the traillevels
        self._trailIndexToPropagate = start

    def _pickBranchLit(self):
        ''' Returns the literal on which we must branch. None if no more
        literals are unassigned. (TODO: this linear scan will be replaced by a heap)'''
        for v in self._order:
            if self._litValues[varToLit(v)] == self._cst.lit_Undef:
                return varToLit(v, 0 if self._config.default_value else 1)
        return None

    def _analyze(self, confl):
        ''' Returns the clause to learn and the level where to backtrack. This clause is
            asserting: its first literal is the only one that is not false at this level.
            DPLL: the decision clause (the negation of all the decisions), and backtrack one level up:
            the last decision is flipped.'''
        decisions = [self._trail[i] for i in self._trailLevels]
        learnt = [notLit(d) for d in reversed(decisions)]          # The last decision first: it will be flipped
        return Clause(learnt, learnt=True), self._decisionLevel() - 1

    def _learn(self, c):
        ''' What to do with the learnt clause. DPLL: nothing, it is forgotten (it is only
            the reason of the flipped decision)'''
        return

    # Simply print the search progress
    def _reportSearch(self):
      s = self._stats
      print("c {cfl:d} conflicts, {dec:d} decisions, {prop:d} propagations, {depth:d} decisions depth".format(cfl=s.conflicts,
        dec=s.decisions,
        prop=s.propagations,
        depth = int(s.sumDecisionLevel / (1 if s.conflicts == 0 else s.conflicts))))

    # The main search procedure: propagate, analyze the conflicts, decide
    def _search(self):
        while True:
            confl = self._propagate()
            if confl is not None:                                         # We reached a conflict
                self._stats.conflicts += 1
                self._stats.sumDecisionLevel += self._decisionLevel()     # stats about the search
                if self._stats.conflicts % 1000 == 0 and self._config.verbosity > 0:
                    self._reportSearch()                                  # reports the search status every 1000 conflicts

                if self._decisionLevel() == 0: return self._cst.lit_False # We proved UNSAT

                learnt, backtrackLevel = self._analyze(confl)
                self._cancelUntil(backtrackLevel)
                self._learn(learnt)
                self._uncheckedEnqueue(learnt[0], learnt)                 # The learnt clause is unit: its first literal is forced
            else:                                                          # No conflict
                l = self._pickBranchLit()                                  # Picks a new variable to branch on
                if l is None: return self._cst.lit_True                    # All variables are assigned and no conflict: SAT was proven
                self._stats.decisions += 1
                self._newDecisionLevel()                                   # Creates a new decision level
                self._uncheckedEnqueue(l)                                  # propagates this literal with no reason (this is a decision)

    def _solve(self):
        # Static heuristic: the variables that occur the most first
        self._order = sorted(range(self._nbvars), key = lambda v: -len(self._occ[varToLit(v)]) - len(self._occ[varToLit(v, 1)]))
        status = self._search()
        if status == self._cst.lit_True:                           # We copy the solution before cancelling the decisions
            self.finalModel = [v+1 if self._litValues[varToLit(v)] == self._cst.lit_True else -v-1 for v in range(self._nbvars)]
        self._cancelUntil(0)                                       # Back to level 0: clauses can be added again
        return status


if __name__ == "__main__":
    runFromCommandLine(DPLL, "DPLL")

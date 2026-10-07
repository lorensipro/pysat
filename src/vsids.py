from watches import *
from satheapq import SatHeapq

class VSIDS(Watches):
    ''' CDCL with watched literals and the VSIDS heuristic (Chaff 2001, in its Minisat version).

        Each variable has an activity. Each variable met during the conflict analysis gets a bump
        (its activity grows by varInc), and after each conflict varInc is multiplied by 1/varDecay:
        the recent conflicts count more than the old ones (an exponential decay of all the
        activities, without touching them). The decision is the unassigned variable of highest
        activity, kept in a heap (the heap of Minisat, in satheapq.py).

        The decisions are now driven by the conflicts: this is the first version, since CDCL, that
        changes the search itself (the number of conflicts), not only the cost of the propagation.'''

    class Configuration(Watches.Configuration):
        ''' Contains all the configuration variables for the solver '''
        varDecay = 0.95                # activities decay (Minisat value)

    def __init__(self):
        super().__init__()
        self._activity = []            # self._activity[v] is the VSIDS score of the variable v
        self._varInc = 1.0             # Amount of each variable bump (multiplied by 1/varDecay after each conflict)
        self._varHeap = SatHeapq(lambda x,y: self._activity[x] > self._activity[y]) # Heap of variables (highest activity first)

        self._stats.addCounter('rescalings', "VSIDS rescalings")   # number of times the activities were rescaled
        return

    def _newVar(self):
        super()._newVar()
        self._activity.append(0.0)
        self._varHeap.insert(self._nbvars - 1)

    def _seenInAnalysis(self, v):
        ''' Bumps the variable met during the conflict analysis. Once in a while, all the
            activities are rescaled (to stay in the range of floats).'''
        self._activity[v] += self._varInc
        if self._activity[v] > 1e100:                              # rescale the activities
            self._stats.rescalings += 1
            for i in range(self._nbvars): self._activity[i] *= 1e-100
            self._varInc *= 1e-100
        if self._varHeap.inHeap(v): self._varHeap.decrease(v)      # Its activity grew: it goes up in the heap

    def _analyze(self, confl):
        result = super()._analyze(confl)
        self._varInc /= self._config.varDecay                      # The next bumps will count more
        return result

    def _pickBranchLit(self):
        ''' Returns the literal on which we must branch: the unassigned variable of highest activity.
            The assigned variables met in the heap are just removed (they are put back by _cancelUntil).'''
        while len(self._varHeap) > 0:
            v = self._varHeap.removeMin()
            if self._litValues[varToLit(v)] == self._cst.lit_Undef:
                return varToLit(v, 0 if self._config.default_value else 1)
        return None

    def _cancelUntil(self, level = 0):
        ''' Backtrack, and put back in the heap the variables that are unassigned '''
        if self._decisionLevel() <= level:
          return
        for x in range(self._trailLevels[level], len(self._trail)):
            v = litToVar(self._trail[x])
            if not self._varHeap.inHeap(v): self._varHeap.insert(v)
        super()._cancelUntil(level)


if __name__ == "__main__":
    runFromCommandLine(VSIDS, "VSIDS")

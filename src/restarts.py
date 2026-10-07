from vsids import *

class Restarts(VSIDS):
    ''' CDCL with VSIDS, restarts and phase saving (Minisat 2.2).

        Restarts: from time to time (after a budget of conflicts), the solver goes back to level 0,
        keeping its learnt clauses and its activities. The first decisions, taken when VSIDS knew
        nothing, are replaced by better ones. The budgets follow a geometric progression (Minisat 1.14)
        or the Luby sequence 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8 ... (Minisat 2.2).

        Phase saving (Pipatsrisawat and Darwiche 2007): the value given to a decision variable is the
        last value it had. After a backtrack (or a restart), the solver goes back to the same part of
        the search space instead of losing the assignments it had already found.'''

    class Configuration(VSIDS.Configuration):
        ''' Contains all the configuration variables for the solver '''
        restarts = 'luby'              # 'none', 'geometric' or 'luby'
        restartFirst = 100             # number of conflicts before the first restart (Minisat values)
        restartInc = 1.5               # factor of the geometric progression
        phaseSaving = True

    def __init__(self):
        super().__init__()
        self._polarity = []            # self._polarity[v] is the sign of the last value of v (1: negative)
        self._conflictsAtRestart = 0   # number of conflicts at the last restart
        self._restartBudget = None     # number of conflicts allowed before the next restart

        self._stats.addCounter('restarts', "restarts")
        return

    def _newVar(self):
        super()._newVar()
        self._polarity.append(0 if self._config.default_value else 1)

    def _decisionLit(self, v):
        if self._config.phaseSaving: return varToLit(v, self._polarity[v])  # The last value of v
        return super()._decisionLit(v)

    def _cancelUntil(self, level = 0):
        ''' Backtrack, saving the values of the unassigned variables '''
        if self._decisionLevel() <= level:
          return
        for x in range(self._trailLevels[level], len(self._trail)):
            l = self._trail[x]
            self._polarity[litToVar(l)] = signLit(l)
        super()._cancelUntil(level)

    def _budget(self, k):
        ''' The number of conflicts allowed before the k-th restart (k = 0, 1, 2...) '''
        if self._config.restarts == 'luby':
            return self._config.restartFirst * luby(2, k)
        return int(self._config.restartFirst * self._config.restartInc ** k)

    def _restartNeeded(self):
        if self._config.restarts == 'none': return False
        if self._restartBudget is None: self._restartBudget = self._budget(0)
        if self._stats.conflicts - self._conflictsAtRestart < self._restartBudget: return False
        self._stats.restarts += 1
        self._conflictsAtRestart = self._stats.conflicts
        self._restartBudget = self._budget(self._stats.restarts)
        return True


if __name__ == "__main__":
    runFromCommandLine(Restarts, "Restarts")

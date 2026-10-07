from restarts import *

class Reduce(Restarts):
    ''' CDCL with the reduction of the learnt clause database.

        A CDCL learns one clause per conflict: after a few thousand conflicts, the learnt clauses
        are much more numerous than the initial ones, and the propagation spends its time in them.
        From time to time, half of them are removed (never the binary ones, nor the reasons of the
        current assignment). Which ones? Two policies:

        'activity' (Minisat 2.2): each learnt clause has an activity, bumped when it is used in a
        conflict analysis (and decaying, as VSIDS for the variables). The database may grow up to
        a maximal size (a third of the initial clauses, growing by 10% at each reduction); the
        least active half is removed.

        'lbd' (Glucose, Audemard and Simon 2009): the LBD of a clause is the number of distinct
        decision levels among its literals, when it is learnt. A clause of small LBD links few
        blocks of propagations: it will be useful again. The clauses of LBD 2 ("glue clauses") are
        kept forever; at each reduction (every 2000 + 300 k conflicts), the half with the largest LBD
        is removed. The LBD of a clause is updated when it is used again in a conflict analysis.'''

    class Configuration(Restarts.Configuration):
        ''' Contains all the configuration variables for the solver '''
        reduce = 'lbd'                 # 'none', 'activity' (Minisat) or 'lbd' (Glucose)
        firstReduce = 2000             # lbd: first reduction after 2000 conflicts...
        incReduce = 300                # ... then 300 more conflicts between two reductions each time (Glucose values)
        learntsFactor = 1.0 / 3        # activity: maximal number of learnt clauses = initial clauses * learntsFactor...
        learntsInc = 1.1               # ... multiplied by learntsInc at each reduction (Minisat values)
        clauseDecay = 0.999            # activity: decay of the clause activities
        updateLBD = True               # lbd: recompute the LBD of the clauses used in conflict analysis

    def __init__(self):
        super().__init__()
        self._clauseInc = 1.0          # Amount of each clause bump (multiplied by 1/clauseDecay after each conflict)
        self._nextReduce = None        # lbd: number of conflicts of the next reduction
        self._maxLearnts = None        # activity: maximal number of learnt clauses before a reduction

        self._stats.addCounter('reductions', "Reductions of the learnt clauses")
        self._stats.addCounter('removedClauses', "Removed learnt clauses", rate='reductions')
        self._stats.addCounter('sumLBD')                                   # sum of the LBD of the learnt clauses
        self._stats.addAverage("Avg LBD of the learnt clauses", 'sumLBD', 'conflicts')
        return

    def _computeLBD(self, c):
        ''' The number of distinct decision levels among the literals of c (all of them have a level) '''
        return len(set(self._level[litToVar(l)] for l in c))

    def _learn(self, c):
        ''' The learnt clause gets its LBD (computed when it is learnt, the asserting literal has still the
            level of the conflict) and its activity '''
        c.lbd = self._computeLBD(c)
        c.activity = 0.0
        self._stats.sumLBD += c.lbd
        super()._learn(c)
        self._bumpClause(c)

    def _bumpClause(self, c):
        c.activity += self._clauseInc
        if c.activity > 1e20:                                      # rescale the activities of the clauses
            for d in self._learnts: d.activity *= 1e-20
            self._clauseInc *= 1e-20

    def _clauseInAnalysis(self, c):
        if not c.learnt: return
        self._bumpClause(c)
        if self._config.updateLBD and c.lbd > 2:                   # The clause may link fewer blocks now
            lbd = self._computeLBD(c)
            if lbd < c.lbd: c.lbd = lbd

    def _analyze(self, confl):
        result = super()._analyze(confl)
        self._clauseInc /= self._config.clauseDecay                # The next bumps will count more
        return result

    def _locked(self, c):
        ''' A clause that is the reason of an assigned literal cannot be removed '''
        return self._reason[litToVar(c[0])] is c and self._litValues[c[0]] == self._cst.lit_True

    def _manageLearnts(self):
        if self._config.reduce == 'lbd':
            if self._nextReduce is None: self._nextReduce = self._config.firstReduce
            if self._stats.conflicts >= self._nextReduce:
                self._reduceDB()
                self._nextReduce = self._stats.conflicts + self._config.firstReduce + self._config.incReduce * self._stats.reductions
        elif self._config.reduce == 'activity':
            if self._maxLearnts is None: self._maxLearnts = len(self._clauses) * self._config.learntsFactor
            if len(self._learnts) - len(self._trail) >= self._maxLearnts:
                self._reduceDB()
                self._maxLearnts *= self._config.learntsInc

    def _reduceDB(self):
        ''' Removes half of the learnt clauses: the worst ones among those that can be removed '''
        self._stats.reductions += 1
        candidates = [c for c in self._learnts if len(c) > 2 and not self._locked(c)]
        if self._config.reduce == 'lbd':
            candidates = [c for c in candidates if c.lbd > 2]      # The glue clauses are kept forever
            candidates.sort(key = lambda c: (-c.lbd, c.activity))  # The largest LBD first (then the least active)
        else:
            candidates.sort(key = lambda c: c.activity)            # The least active first
        for c in candidates[:len(self._learnts) // 2]:
            c.removed = True
            self._stats.removedClauses += 1
        self._learnts = [c for c in self._learnts if not getattr(c, 'removed', False)]
        for l in range(2 * self._nbvars):                          # The removed clauses leave the watch lists
            self._watches[l] = [c for c in self._watches[l] if not getattr(c, 'removed', False)]
            self._occ[l] = [c for c in self._occ[l] if not getattr(c, 'removed', False)]


if __name__ == "__main__":
    runFromCommandLine(Reduce, "Reduce")

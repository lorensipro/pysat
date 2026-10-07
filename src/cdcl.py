from dpll import *

class CDCL(DPLL):
    ''' The CDCL algorithm (GRASP, Marques-Silva and Sakallah 1996): DPLL with conflict analysis,
        clause learning and non chronological backtracking.

        Only two methods of DPLL are redefined: _analyze learns a better clause than the
        decision clause (the first UIP), and _learn keeps it. Everything else (propagation with
        counters, static heuristic, no restarts) is the same, to see the effect of learning alone.'''

    def __init__(self):
        super().__init__()
        self._learnts = []             # The learnt clauses
        self._seen = []                # self._seen[v] marks the variables met during the conflict analysis

        self._stats.addCounter('resolutions', "Resolutions", rate='conflicts')  # resolution steps during the conflict analysis
        self._stats.addCounter('sumLearntSize')                                  # sum of the sizes of the learnt clauses
        self._stats.addAverage("Avg learnt clause size", 'sumLearntSize', 'conflicts')
        self._stats.addCounter('sumBackjump')                                    # sum of the number of levels jumped back
        self._stats.addAverage("Avg backjump (levels)", 'sumBackjump', 'conflicts')
        return

    def _newVar(self):
        super()._newVar()
        self._seen.append(False)

    def _analyze(self, confl):
        ''' Conflict analysis with the first UIP scheme. We start from the conflict and replace
            (by resolution) each literal of the current decision level by its reason, in the reverse
            order of the trail, until only one literal of the current level is left: the first UIP.
            Returns the learnt clause (the negation of the UIP first, then the literal of the highest
            level in position 1) and the level where to backtrack: the second highest level of the clause.'''
        seen = self._seen
        learnt = [None]                # We leave a room for the asserting literal in place 0
        pathC = 0                      # Number of literals of the current level still to remove
        p = None                       # The literal of the trail whose reason is c (None for the conflict itself)
        c = confl
        index = len(self._trail) - 1
        while True:
            if p is not None: self._stats.resolutions += 1
            self._clauseInAnalysis(c)
            for q in c:
                v = litToVar(q)
                if p is not None and v == litToVar(p): continue    # (the literal propagated by this reason)
                if not seen[v] and self._level[v] > 0:             # (literals of level 0 are false forever: useless)
                    seen[v] = True
                    self._seenInAnalysis(v)
                    if self._level[v] == self._decisionLevel():
                        pathC += 1                                 # one more literal of the current level, to remove
                    else:
                        learnt.append(q)                           # q stays in the learnt clause
            while not seen[litToVar(self._trail[index])]: index -= 1 # The next seen literal of the trail
            p = self._trail[index]
            index -= 1
            seen[litToVar(p)] = False
            pathC -= 1
            if pathC == 0: break                                   # p is the first UIP
            c = self._reason[litToVar(p)]                          # c propagated p: all its other literals are false

        learnt[0] = notLit(p)                                      # The asserting literal
        for l in learnt[1:]: seen[litToVar(l)] = False             # remove the remaining seen tags

        backtrackLevel = 0
        if len(learnt) > 1:                                        # The literal of the highest level goes in position 1
            imax = max(range(1, len(learnt)), key = lambda i: self._level[litToVar(learnt[i])])
            learnt[1], learnt[imax] = learnt[imax], learnt[1]
            backtrackLevel = self._level[litToVar(learnt[1])]
        self._stats.sumLearntSize += len(learnt)
        self._stats.sumBackjump += self._decisionLevel() - backtrackLevel
        return Clause(learnt, learnt=True), backtrackLevel

    def _clauseInAnalysis(self, c):
        ''' Called for each clause used during the conflict analysis (the conflict, then the reasons) '''
        return

    def _seenInAnalysis(self, v):
        ''' Called for each variable met during the conflict analysis (used by the heuristics) '''
        return

    def _learn(self, c):
        ''' The learnt clause is kept, and attached for the propagation '''
        self._learnts.append(c)
        self._attachClause(c)


if __name__ == "__main__":
    runFromCommandLine(CDCL, "CDCL")

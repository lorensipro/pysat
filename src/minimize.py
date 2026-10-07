from reduce import *

class Minimize(Reduce):
    ''' CDCL with the minimization of the learnt clauses (Minisat 2, Sörensson and Biere 2009).

        A literal of the learnt clause is redundant when it is implied by the other literals of the
        clause: removing it gives a shorter clause, still implied by the formula, which propagates
        sooner and costs less to watch.

        'local': the literal l is removed when all the other literals of its reason are already in
        the clause (or false at level 0): resolving l with its reason adds nothing.

        'recursive': the same question is asked again for the literals of the reason that are not in
        the clause, following the implication graph backwards, until it reaches literals of the clause
        (redundant) or a decision (not redundant). A filter on the decision levels (a small Bloom
        filter of the levels of the clause, the "abstract levels") stops early the hopeless paths.'''

    class Configuration(Reduce.Configuration):
        ''' Contains all the configuration variables for the solver '''
        minimize = 'recursive'         # 'none', 'local' or 'recursive' (Minisat 2.2)

    def __init__(self):
        super().__init__()
        self._stats.addCounter('minimizedLits', "Literals removed by minimization", rate='conflicts')
        return

    def _abstractLevel(self, v):
        ''' One bit for the decision level of v (among 32): a Bloom filter of the levels '''
        return 1 << (self._level[v] & 31)

    def _minimize(self, learnt):
        mode = self._config.minimize
        if mode == 'none' or len(learnt) <= 2: return learnt
        seen = self._seen
        kept = [learnt[0]]
        if mode == 'local':
            for l in learnt[1:]:
                r = self._reason[litToVar(l)]
                if r is None or any(not seen[litToVar(x)] and self._level[litToVar(x)] > 0
                                    for x in r if litToVar(x) != litToVar(l)):
                    kept.append(l)                                 # (a decision, or a reason that brings new literals)
        else:
            abstractLevels = 0
            for l in learnt[1:]: abstractLevels |= self._abstractLevel(litToVar(l))
            marked = []                                            # The variables proven redundant on the way (seen)
            for l in learnt[1:]:
                if self._reason[litToVar(l)] is None or not self._litRedundant(l, abstractLevels, marked):
                    kept.append(l)
            for x in marked: seen[litToVar(x)] = False
        self._stats.minimizedLits += len(learnt) - len(kept)
        return kept

    def _litRedundant(self, l, abstractLevels, marked):
        ''' Is the literal l (false, propagated) implied by the literals of the clause (the seen ones)?
            Depth first search in the implication graph, backwards from l. The variables proven
            redundant are marked as seen (and kept in marked); if l is not redundant, the marks of
            this search are removed.'''
        seen = self._seen
        stack = [l]
        top = len(marked)
        while stack:
            q = stack.pop()
            for x in self._reason[litToVar(q)]:
                v = litToVar(x)
                if v == litToVar(q) or seen[v] or self._level[v] == 0: continue
                if self._reason[v] is not None and (self._abstractLevel(v) & abstractLevels) != 0:
                    seen[v] = True                                 # To be proven: we go on with its reason
                    stack.append(x)
                    marked.append(x)
                else:                                              # A decision, or a level not in the clause: l stays
                    for y in marked[top:]: seen[litToVar(y)] = False
                    del marked[top:]
                    return False
        return True


if __name__ == "__main__":
    runFromCommandLine(Minimize, "Minimize")

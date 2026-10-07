from dpll import *

class Lookahead(DPLL):
    ''' DPLL with a lookahead heuristic (in the spirit of POSIT, Satz, kcnfs, march).

        At each node, before deciding, each free variable x is tried: x is assumed and propagated,
        then the opposite literal. If one of them leads to a conflict (a failed literal), the other one
        is implied: it is fixed at the current level and propagated. Otherwise, the decision is the
        variable whose two branches propagate the most literals, in a balanced way.

        Thinking before trying: the search tree is much smaller, but each node is much more expensive.'''

    class Configuration(DPLL.Configuration):
        ''' Contains all the configuration variables for the solver '''
        candidates = None              # number of free variables tried at each node (None: all of them),
                                       # the first ones in the static order

    def __init__(self):
        super().__init__()
        self._bestVar = None           # The decision chosen by the last lookahead

        self._stats.addCounter('lookaheads', "Lookaheads (literals tried)", rate='decisions')
        self._stats.addCounter('failedLiterals', "Failed literals")
        return

    def _candidates(self):
        ''' The free variables tried by the lookahead '''
        free = [v for v in self._order if self._litValues[varToLit(v)] == self._cst.lit_Undef]
        return free if self._config.candidates is None else free[:self._config.candidates]

    def _try(self, l):
        ''' Assumes l and propagates it (on a new decision level, cancelled right after). Returns
            the number of literals assigned (l included), or None if l fails (a conflict).'''
        self._stats.lookaheads += 1
        level = self._decisionLevel()
        start = len(self._trail)
        self._newDecisionLevel()
        self._uncheckedEnqueue(l)
        confl = self._propagate()
        n = len(self._trail) - start
        self._cancelUntil(level)
        return None if confl is not None else n

    def _fix(self, l):
        ''' The opposite of l failed: l is implied at the current level (in DPLL, no reason is needed:
            it will be undone with this level, when the decision of this level is flipped)'''
        self._stats.failedLiterals += 1
        self._uncheckedEnqueue(l)
        return True

    def _simplifyNode(self):
        ''' The lookahead: each candidate variable is tried in both directions '''
        self._bestVar = None
        bestScore = -1
        for v in self._candidates():
            pos = self._try(varToLit(v))
            if pos is None: return self._fix(varToLit(v, 1))       # v fails: -v is implied
            neg = self._try(varToLit(v, 1))
            if neg is None: return self._fix(varToLit(v))          # -v fails: v is implied
            score = pos * neg * 1024 + pos + neg                   # Both branches must reduce the formula
            if score > bestScore:
                self._bestVar = v; bestScore = score
        return False                                               # No failed literal: the decision is self._bestVar

    def _pickBranchLit(self):
        if self._bestVar is None: return super()._pickBranchLit()  # (no candidate: the static order)
        return varToLit(self._bestVar, 0 if self._config.default_value else 1)


class DoubleLookahead(Lookahead):
    ''' Lookahead with a second level: when trying l, a lookahead is done again under l. If a
        variable y fails in both directions under l, then l fails too (even if its propagation
        alone gives no conflict). More failed literals are found, for a quadratic cost.'''

    def __init__(self):
        super().__init__()
        self._stats.addCounter('doubleFailed', "Failed literals found by the second level")
        return

    def _try(self, l):
        self._stats.lookaheads += 1
        level = self._decisionLevel()
        start = len(self._trail)
        self._newDecisionLevel()
        self._uncheckedEnqueue(l)
        confl = self._propagate()
        n = len(self._trail) - start
        if confl is None:                                          # Second level: a variable that fails both ways under l
            for v in self._candidates():
                if Lookahead._try(self, varToLit(v)) is None and Lookahead._try(self, varToLit(v, 1)) is None:
                    self._stats.doubleFailed += 1
                    confl = v
                    break
        self._cancelUntil(level)
        return None if confl is not None else n


if __name__ == "__main__":
    runFromCommandLine(DoubleLookahead if '--double' in sys.argv else Lookahead, "Lookahead")

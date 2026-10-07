from cdcl import *

class Watches(CDCL):
    ''' CDCL with the 2-watched literals of Chaff (Moskewicz, Madigan, Zhao, Zhang, Malik, 2001).

        Instead of updating counters in all the clauses of a literal (CDCL), only two literals of each
        clause are watched (here c[0] and c[1]), and a clause is only visited when one of them becomes
        false. As in SATO (a branch of CDCL, to compare with), but the watched literals can be anywhere
        in the clause and move in any direction, and nothing is required from the other literals.
        Unassigning a literal can never break this: when backtracking, there is nothing to restore
        (see _unpropagateLit, which is empty).'''

    def __init__(self):
        super().__init__()
        self._watches = []             # self._watches[l] is the list of the clauses watching l (c[0] or c[1] is l)

        self._stats.addCounter('pointerMoves', "Watch moves", rate='propagations')
        return

    def _newVar(self):
        super()._newVar()
        self._watches += [[], []]

    def _attachClause(self, c):
        ''' The clause is watched by its two first literals. It must be called when all the literals
            of the trail are propagated: at level 0 all the literals are unassigned, and in a learnt
            clause c[0] is the asserting literal and c[1] the false literal of the highest level
            (they will both be unassigned after any backtrack that unassigns another literal)'''
        assert self._trailIndexToPropagate == len(self._trail)
        for l in c: self._occ[l].append(c)                         # (only used by the static heuristic)
        if len(c) == 1: return                                     # A unary clause is propagated once, at level 0
        self._watches[c[0]].append(c)
        self._watches[c[1]].append(c)

    def _propagateLit(self, l):
        ''' The literal l (already true) is propagated: notLit(l) becomes false, the clauses that
            watch it look for another watch. Returns a conflict or None.'''
        litValues = self._litValues                                # local variable: faster in the loop
        stats = self._stats
        falseLit = notLit(l)
        conflict = None
        wl = self._watches[falseLit]
        i = 0; j = 0
        while i < len(wl):
            c = wl[i]; i += 1
            stats.clauseVisits += 1
            if conflict is not None:                               # After a conflict, the watches are just kept
                wl[j] = c; j += 1
                continue
            if c[0] == falseLit:                                   # Make sure the false literal is in 1
                c[0] = c[1]; c[1] = falseLit
            if litValues[c[0]] == self._cst.lit_True:              # The clause is already satisfied (by the other watch)
                wl[j] = c; j += 1
                continue

            moved = False
            for k in range(2, len(c)):                             # Remember that c[0] and c[1] are special
                if litValues[c[k]] != self._cst.lit_False:         # Found a new (not false) watch
                    c[1] = c[k]; c[k] = falseLit
                    self._watches[c[1]].append(c)                  # c leaves this list (it is not copied in wl[j])
                    stats.pointerMoves += 1
                    moved = True
                    break
            if moved: continue

            wl[j] = c; j += 1                                      # No new watch: c stays watched by falseLit
            if litValues[c[0]] == self._cst.lit_False:             # All the literals are false: a conflict
                conflict = c
            else:                                                  # The clause is unit: c[0] is forced
                self._uncheckedEnqueue(c[0], c)
        del wl[j:]                                                 # pythonic way to remove the unused tail of the list
        return conflict

    def _unpropagateLit(self, l):
        ''' Nothing to do: the watches stay valid when literals are unassigned.'''
        return


if __name__ == "__main__":
    runFromCommandLine(Watches, "Watched literals")

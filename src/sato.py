from cdcl import *

class SATO(CDCL):
    ''' CDCL with the head/tail lists of SATO (H. Zhang, 1997) for the unit propagation.

        Each clause has two pointers: head (starting from the left) and tail (starting from the
        right). The invariant: all the literals before head and after tail are false. A clause is
        only visited when its head or its tail literal becomes false: the pointer then moves
        towards the other one, over the false literals. When they meet, the clause is unit (or
        conflicting, or satisfied).

        The pointers only move inwards: when backtracking, they must be put back where they were
        (see _unpropagateLit). Each move is written in a journal, undone in the reverse order.
        The counters of DPLL are not used anymore.'''

    def __init__(self):
        super().__init__()
        self._watches = []             # self._watches[l] is the list of the clauses whose head or tail literal is l
        self._journal = []             # The pointer moves: (clause, isHead, old position), in the order of the trail
        self._journalStart = []        # self._journalStart[v]: size of the journal when the literal of v was propagated

        self._stats.addCounter('pointerMoves', "Pointer moves", rate='propagations')
        return

    def _newVar(self):
        super()._newVar()
        self._watches += [[], []]
        self._journalStart.append(0)

    def _attachClause(self, c):
        ''' The clause gets its two pointers. It must be called when all the literals of the
            trail are propagated (at level 0, or just after a backtrack).
            At level 0, all the literals are unassigned. For a learnt clause, all the literals are
            false except the first one: the tail is put on the false literal of the highest
            level (at the end), so that the invariant still holds after any backtrack.'''
        assert self._trailIndexToPropagate == len(self._trail)
        for l in c: self._occ[l].append(c)                         # (only used by the static heuristic)
        if len(c) == 1: return                                     # A unary clause is propagated once, at level 0
        if c.learnt: c[1], c[-1] = c[-1], c[1]                     # CDCL put the literal of the highest level in position 1
        c.head = 0
        c.tail = len(c) - 1
        self._watches[c[c.head]].append(c)
        self._watches[c[c.tail]].append(c)

    def _propagateLit(self, l):
        ''' The literal l (already true) is propagated: notLit(l) becomes false, the clauses whose
            head or tail is notLit(l) move this pointer. Returns a conflict or None.'''
        litValues = self._litValues                                # local variable: faster in the loop
        stats = self._stats
        falseLit = notLit(l)
        self._journalStart[litToVar(l)] = len(self._journal)       # The moves of this propagation start here
        conflict = None
        wl = self._watches[falseLit]
        i = 0; j = 0
        while i < len(wl):
            c = wl[i]; i += 1
            stats.clauseVisits += 1
            if c[c.head] == falseLit: isHead = True
            elif c[c.tail] == falseLit: isHead = False
            else: continue                                         # An old entry (the pointer has moved since): dropped
            if conflict is not None:                               # After a conflict, the watches are just kept
                wl[j] = c; j += 1
                continue

            if isHead:                                             # The head moves to the right, over the false literals
                k = c.head + 1
                while k < c.tail and litValues[c[k]] == self._cst.lit_False: k += 1
                moved = k < c.tail
            else:                                                  # The tail moves to the left
                k = c.tail - 1
                while k > c.head and litValues[c[k]] == self._cst.lit_False: k -= 1
                moved = k > c.head

            if moved:                                              # A new literal (not false) for this pointer
                self._journal.append((c, isHead, c.head if isHead else c.tail))
                if isHead: c.head = k
                else: c.tail = k
                self._watches[c[k]].append(c)                      # c leaves this list (it is not copied in wl[j])
                stats.pointerMoves += 1
                continue

            wl[j] = c; j += 1                                      # The pointers met: c stays watched by falseLit
            other = c[c.tail] if isHead else c[c.head]             # The only literal of c that may not be false
            if litValues[other] == self._cst.lit_False:            # All the literals are false: a conflict
                conflict = c
            elif litValues[other] == self._cst.lit_Undef:          # The clause is unit: other is forced
                self._uncheckedEnqueue(other, c)
                                                                   # (if other is true, the clause is satisfied)
        del wl[j:]                                                 # pythonic way to remove the unused tail of the list
        return conflict

    def _unpropagateLit(self, l):
        ''' Puts back the pointers moved by the propagation of l, in the reverse order. Each clause
            is watched again by its old literal (its entry in the other list becomes an old one,
            dropped when met).'''
        start = self._journalStart[litToVar(l)]
        while len(self._journal) > start:
            c, isHead, old = self._journal.pop()
            if isHead: c.head = old
            else: c.tail = old
            self._watches[c[old]].append(c)
            self._stats.clauseRestores += 1


if __name__ == "__main__":
    runFromCommandLine(SATO, "SATO")

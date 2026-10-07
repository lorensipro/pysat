from minimize import *

class VMTF(Watches):
    ''' CDCL with watched literals and the VMTF heuristic (Variable Move-To-Front: Ryan 2004, evaluated by
        Biere and Fröhlich 2015, used by CaDiCaL and Kissat in their focused mode). To compare with VSIDS.

        The variables are kept in a doubly linked list (a queue). After each conflict, the variables met
        during the analysis are moved to the end of the queue (in the order of their previous positions).
        The decision is the last unassigned variable of the queue. No score, no heap, no rescaling: the
        position in the queue is the only memory of the conflicts.

        To find the decision quickly, a pointer (_searchPointer) remembers a position such that all the variables
        after it are assigned. The decision goes backwards from it; when backtracking, an unassigned
        variable that is after the pointer moves the pointer to it. Each variable has a stamp (its time of
        enqueueing) to compare the positions.'''

    def __init__(self):
        super().__init__()
        self._prev = []                # self._prev[v], self._next[v]: the neighbours of v in the queue (None at the ends)
        self._next = []
        self._stamp = []               # self._stamp[v]: the time v was (re)enqueued; larger stamps are nearer to the end
        self._first = None             # The first and the last variables of the queue
        self._last = None
        self._searchPointer = None     # All the variables after this one in the queue are assigned
        self._time = 0                 # The last stamp given

        self._stats.addCounter('moveToFront', "VMTF moves to front", rate='conflicts')
        return

    def _newVar(self):
        super()._newVar()
        self._prev.append(None); self._next.append(None); self._stamp.append(0)
        self._varEnqueue(self._nbvars - 1)
        self._searchPointer = self._last

    def _varDequeue(self, v):
        ''' Removes the variable v from the VMTF queue (not to be confused with the propagation queue of the trail) '''
        p, n = self._prev[v], self._next[v]
        if p is None: self._first = n
        else: self._next[p] = n
        if n is None: self._last = p
        else: self._prev[n] = p
        self._prev[v] = self._next[v] = None

    def _varEnqueue(self, v):
        ''' Puts the variable v at the end of the VMTF queue, with a new stamp '''
        self._prev[v] = self._last
        self._next[v] = None
        if self._last is None: self._first = v
        else: self._next[self._last] = v
        self._last = v
        self._time += 1
        self._stamp[v] = self._time

    def _bumpVariables(self, analyzed):
        ''' The variables met during the conflict analysis move to the end of the queue, in the order of
            their previous positions (they are all assigned: the search pointer stays valid)'''
        for v in sorted(analyzed, key = lambda v: self._stamp[v]):
            if v != self._last:
                self._varDequeue(v)
                self._varEnqueue(v)                                  # Move to front (the end of the queue)
                self._stats.moveToFront += 1

    def _pickBranchLit(self):
        ''' The last unassigned variable of the queue, searched backwards from the pointer '''
        v = self._searchPointer
        while v is not None and self._litValues[varToLit(v)] != self._cst.lit_Undef:
            v = self._prev[v]
        self._searchPointer = v
        if v is None: return None
        return self._decisionLit(v)

    def _cancelUntil(self, level = 0):
        ''' Backtrack: an unassigned variable after the search pointer becomes the new pointer '''
        if self._decisionLevel() <= level:
          return
        for x in range(self._trailLevels[level], len(self._trail)):
            v = litToVar(self._trail[x])
            if self._searchPointer is None or self._stamp[v] > self._stamp[self._searchPointer]: self._searchPointer = v
        super()._cancelUntil(level)


class MinimizeVMTF(VMTF, Minimize):
    ''' The whole chain (restarts, phase saving, reduction by LBD, minimization) with VMTF instead of VSIDS.

        Nothing to write: the two branches are combined by multiple inheritance. Python looks for the methods
        in the order MinimizeVMTF, VMTF, Minimize, Reduce, Restarts, VSIDS, Watches, CDCL, DPLL, Solver: the
        methods of VMTF (decision, move to front) come before the ones of VSIDS, everything else comes from
        the chain. This works because each method calls super() (VSIDS still maintains its heap, unused).'''


if __name__ == "__main__":
    runFromCommandLine(MinimizeVMTF if '--full' in sys.argv else VMTF, "VMTF")

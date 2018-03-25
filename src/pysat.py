import pdb # debugger
from array import *
import time, sys

# My imports
from satutils import *
from sattypes import *
from satheapq import *
from satboundedqueue import *
from prettyPrinter import *


class Constants():
    '''Constants used inside the solver and outside, to read the search status'''
    lit_False = 0
    lit_True = 1
    lit_Undef = 2

class Solver():
    ''' Some function names are taken from the Minisat interface '''
    _cst = Constants()

    class Configuration():
        ''' Contains all the configuration variables for the solver '''
        varDecay = 0.95
        default_value = False    # default value for branching
        verbosity = 1
        printModel = False
        restartInc = 2                         # restart interval factor (as in Minisat)
 
    _config = None            # Configuration of this solver
    _nbvars = 0               # Number of variables
    _scores = MyArray('d')    # Array of doubles, score (VSIDS) of each variable (not literals)
    _varHeap = None           # Heap (that can update scores) of variables
    _clauses = []             # Simply the list of initial clauses
    _learnts = []             # List of learnt clauses
    _reason = MyList()        # _reason[v] is the clause that propagated the literal v or -v (or None if v,-v was a decision)
    _watches = MyList()       # list of watched clauses by this literal
    _values = MyArray('b')    # Current assigned values for each variable (in Constants())
    _polarity = MyArray('b')  # used for the simple phase caching scheme
    _seen = MyArray('b')      # seen array used to mark variables during conflict analysis
    _level = MyArray('I')     # decision level of this assigned variable
    _varInc = 1               # Amount of each variable bump (multiplied by 1/varDecay after each conflict)
    
    _flags = MyArray('I')     # Used to mark variables (for LBD computation)
    _flag = 0
    _finalModel = []          # the model (if SAT) will be copied in this array of variables)

    # statistics
    _conflicts = 0          # total number of conflicts
    _restarts = 0
    _propagations = 0       # total number of propagations
    _propMoves = 0          # number of times a watched was moved
    _watchesInspections = 0 # number of inspected clauses during propagations
    _rescaling = 0          # number of times scores were rescaled
    _sumDecisionLevel = 0
    _sumTrailSize = 0
    _resolutions = 0
    _unaryClauses = 0

    # Propagation Queue
    _trail = MyList()          # trail representing the current partial assignment (trail of literals)
    _trailLevels = MyList()    # Splits the trail in levels
    _trailIndexToPropagate = 0 # Handles the propagation queue. Literals in _trail (strictly) above are already propagated

    def __init__(self, config=None):
        if config == None:
            config = self.Configuration()
        self._time0 = time.time()
        self._config = config
        self._varHeap = SatHeapq(lambda x,y: self._scores[x] > self._scores[y]) 
        return
    
    def _valueLit(self, l):
        v,s = litToVarSign(l)
        if self._values[v] is self._cst.lit_Undef: return self._cst.lit_Undef
        if s:
            return self._cst.lit_False if self._values[v] is self._cst.lit_True  else self._cst.lit_True
        return self._values[v]

    def _pickBranchLit(self):
        ''' Returns the literal on which we must branch. None if no more
        literals are unassigned. We score the variables, then pick a polarity
        according to another heuristics.'''
        v = None
        while len(self._varHeap._heap) > 0:
            v = self._varHeap.removeMin()
            if self._values[v] == self._cst.lit_Undef: break
        if v == None or self._values[v] != self._cst.lit_Undef: return None
        return varToLit(v, not self._config.default_value)                 # literal is negative if default_value is False
    
    def _cancelUntil(self, level = 0):
        ''' Backtrack to the given level (undoing everything). Real magic function where
            almost nothing has to be done, thanks to the 2-literals scheme.'''
        if len(self._trailLevels) <= level: return
        x = len(self._trail) - 1
        while x > self._trailLevels[level] - 1:
            l = self._trail[x]
            self._polarity[litToVar(l)] = signLit(l)  # Memorizes the polarity for branching there next time the variable
                                                      # is selected by pickbranchlit
            self._values[litToVar(l)] = self._cst.lit_Undef
            if not self._varHeap.inHeap(litToVar(l)):
                self._varHeap.insert(litToVar(l))
            x -= 1
        del self._trail[self._trailLevels[level] - len(self._trail):] # shrinks the trail
        self._trailIndexToPropagate = self._trailLevels[level]
        del self._trailLevels[level - len(self._trailLevels):]        # shrinks the traillevels
        
    def _newDecisionLevel(self):
        self._trailLevels.append(len(self._trail))

    def _decisionLevel(self):
        return len(self._trailLevels)
    
    def _uncheckedEnqueue(self, l, r=None):
        ''' Enqueue a literal l to the propagation queue.
            This is unchecked in the sense that no contradiction can be detected'''
        v,s = litToVarSign(l)
        assert self._values[v] == self._cst.lit_Undef # Checks that the literal was not already assigned
        self._values[v] = self._cst.lit_False if s else self._cst.lit_True
        self._reason[v] = r
        self._level[v] = self._decisionLevel()
        self._trail.append(l)
    
    def _varBump(self, v):
        '''Bumps the given variable, used during conflict analysis. Once in while this
           function may rescale all the scores.'''
        self._scores[v] += self._varInc
        if self._scores[v] > 1e100: # rescale the scores
            self._rescaling += 1
            for i in range(0,len(self._scores)): self._scores[i] *= 1e-100
            self._varInc *= 1e-100
        if self._varHeap.inHeap(v): self._varHeap.decrease(v)      # This is a lazy bump: assigned variables will be replaced during cancelUntil

    def _propagate(self):
        ''' Can return a conflict or None 
            This version uses 2-watched literals'''
        while self._trailIndexToPropagate < len(self._trail):
            self._propagations += 1
            litToPropagate = self._trail[self._trailIndexToPropagate]
            #printTrail(self)
            #printClauses(self, lambda x : self._valueLit(x) != cst.lit_Undef, lambda x : self._valueLit(x) == cst.lit_True)
            self._trailIndexToPropagate += 1
            i = 0; j = 0; wl = self._watches[litToPropagate]       # wl is the list of watched clauses to inspect 
            while i < len(wl):
                self._watchesInspections += 1
                c = wl[i];                                         # c is a clause containing -litToPropagate watched by it
                foundNewWatch = False
                assert notLit(litToPropagate)==c[0] or notLit(litToPropagate)==c[1] # Strong assertion introduced in Minisat 
                assert len(c) > 1                                  # Clauses of size 1 are just untailed literals at level 0
                if c[0] == notLit(litToPropagate):
                    c[0]=c[1]; c[1]=notLit(litToPropagate)         # Make sure the false literal is in 1

                if self._valueLit(c[0]) == self._cst.lit_True:           # The clause is already satisfied (by the other watch)
                    wl[j] = c; j+=1; i+=1
                    continue

                for k in range(2,len(c)):                          # Remember that c[0] and c[1] are special
                    l = c[k]
                    if self._valueLit(l) != self._cst.lit_False: 
                        assert c[k] == l
                        c[k]=c[1]; c[1]=l                          # moves the watched literal to c[1]
                        self._watches[notLit(l)].append(c)         # now this clause is watched by l instead of litToPropagate
                        self._propMoves += 1
                        i+=1                                       # wl[i] will not be copied to any smaller wl[j]
                        foundNewWatch = True                       # Don't propagate anything, the clause is satisfied
                        break                                      # Stop inspecting the current clause
                
                if foundNewWatch: 
                    continue
                
                if self._valueLit(c[0]) == self._cst.lit_False:          # The clause is empty
                    while i < len(wl):                             # Copy remaining watches, preparing for a clean early exit
                        wl[j] = wl[i]; j+=1; i+=1
                    if j < i: del wl[j-i:]                         # pythonic way to remove the unused tail of watched list
                    self._trailIndexToPropagate = len(self._trail) # No more literal to propagate
                    return c                                       # the empty clause to return
                else:                                              # The clause is unary (and c[1] is forced)
                    self._uncheckedEnqueue(c[0], c)                # Enqueue it (side effect on len(self._trail))
                    wl[j] = wl[i]; j+=1; i+=1                      # The clause is still watched by litToPropagate
            if j < i: del wl[j-i:]                                 # We traversed all the watches of litToPropagate, remove moved ones
        return None

    def _analyze(self, c):
        learnt = [0] # We leave a room for the asserting literal in place 0
        pathC = 0    # Current number of literals from the last decision level in the conflict analysis
        p = None
        index = len(self._trail) - 1
        backtrackLevel = 0 # Keep track of the largest level in the final clause
        maxbl = -1         # Index of the literal with the largest level (needed to put it in c[1] at the end)
        while True:
            if p is not None: self._resolutions += 1
            for j in range(0 if p is None else 1, len(c)):
                q = c[j]
                if (self._seen[litToVar(q)]==0) and (self._level[litToVar(q)] > 0):
                    self._varBump(litToVar(q))
                    self._seen[litToVar(q)] = 1
                    if self._level[litToVar(q)] == self._decisionLevel():
                        pathC += 1                                          # one more literal in the conflict level (to remove)
                    else:
                        learnt.append(q)                                    # q is a literal in the learnt clause
                        if self._level[litToVar(q)] > backtrackLevel:       # Updates the backtrackLevel
                            backtrackLevel = self._level[litToVar(q)]
                            maxbl = len(learnt) - 1
            while not self._seen[litToVar(self._trail[index])]: index -= 1
            p = self._trail[index]
            c = self._reason[litToVar(p)]
            self._seen[litToVar(p)] = 0
            index -= 1
            pathC -= 1
            if pathC == 0: break

        learnt[0] = notLit(p)                                               # The asserting literal (FUIP, where to backtrack)
        for i in range(1,len(learnt)): self._seen[litToVar(learnt[i])] = 0  # remove the remaining seen tags

        if len(learnt) > 1: 
            p = learnt[maxbl]; learnt[maxbl] = learnt[1]; learnt[1] = p

        # computes the LBD
        lbd = 2
        return learnt, backtrackLevel, lbd

    def addClause(self, listOfInts):
        self._clauses.append(Clause([intToLit(l) for l in listOfInts]))
        self._nbvars = max(self._nbvars, max(abs(i) for i in listOfInts))

    def buildDataStructure(self): 
        starttime = time.time()

        self._values.growTo(self._nbvars, self._cst.lit_Undef)
        for e in [self._values, self._scores, self._polarity, self._reason, self._seen, self._level]:
            e.growTo(self._nbvars)
        self._watches.growTo(self._nbvars * 2, [])

        for i in range(0,self._nbvars): self._polarity[i] = self._config.default_value; # Fills the default polarity
        
        for c in self._clauses:
            if len(c)==1:
                self._uncheckedEnqueue(c[0]) #FIXME I need to check here if there is a contradiction
            for l in c[0:2]: 
                self._watches[notLit(l)].append(c)
                self._scores[litToVar(l)] += 1

        for i in range(0,self._nbvars): self._varHeap.insert(i)     # push all the variables on the heap

        print("c Building data structures in {t:03.2f}s".format(t=time.time()-starttime))
        print("c Ready to go with {v:d} variables and {c:d} clauses".format(v=self._nbvars, 
                  c=len(self._clauses)))
 
    def _checkRestart(self):
        ''' Checks if a restart is needed ''' #TODO (only fixed restarts strategies are implemented)
        return False
    
    def _checkDBReduce(self):
        ''' Check and reduce the learnt clause database if needed ''' #TODO (no cleaning strategies yet)
        return

    def _attachClause(self, c):
        self._watches[notLit(c[0])].append(c) # This will attach the clause
        self._watches[notLit(c[1])].append(c) # attach clause, second watched

    # Simply print the search progress
    def _reportSearch(self):
      print("c {cfl:d} conflicts, {prop:d} propagations, {rest:d} restarts, {una:d}/{unalearnts:d} unaries, {depth:d} decisions depth, {propdepth:d} propagation depth, {res:d} resolutions".format(cfl=self._conflicts,
        prop=self._propagations, 
        rest=self._restarts, 
        una=self._trailLevels[0], 
        unalearnts = self._unaryClauses, 
        depth = int(self._sumDecisionLevel / (1 if self._conflicts is 0 else self._conflicts)),
        propdepth = int(self._sumTrailSize / (1 if self._conflicts is 0 else self._conflicts)),
        res=self._resolutions)) 

    # The main CDCL search procedure, limited to "budget" conflicts
    def _search(self, budget=None):
        conflictC = 0                                              # Number of conflicts for this search

        while budget is None or conflictC < budget:
            confl = self._propagate()
            if confl is not None:                                         # We reached a conflict
                conflictC += 1; self._conflicts += 1

                self._sumDecisionLevel += self._decisionLevel()           # stats about the search
                self._sumTrailSize += len(self._trail)

                if self._conflicts % 100 == 0: self._reportSearch()       # reports the search status evert 100 conflicts

                if self._decisionLevel() is 0: return self._cst.lit_False # We proved UNSAT

                nc, backtrackLevel, lbd = self._analyze(confl)            # TODO: the lbd mechanism is not implemented
                self._varInc /= self._config.varDecay
                self._cancelUntil(backtrackLevel)
                if len(nc)==1:                                            # We don't learn unary clauses. We just push them (the above backtrackLevel is 0)
                    assert backtrackLevel is 0
                    self._unaryClauses += 1
                    self._uncheckedEnqueue(nc[0])
                else:
                    ncc = Clause(nc, learnt=True, lbd=lbd)
                    self._learnts.append(ncc)
                    self._attachClause(ncc)
                    self._uncheckedEnqueue(nc[0],ncc)
            else:                                                          # No conflict
                if self._checkRestart(): break                             # triggers a restart (dynamic strategues)
                self._checkDBReduce()                                      # We may need to clean up the set of learnt clauses

                l = self._pickBranchLit()                                  # Picks a new variable to branch on
                if l == None: return self._cst.lit_True                    # All variables are assigned and no conflict: SAT was proven
                self._newDecisionLevel()                                   # Creates a new decision level
                self._uncheckedEnqueue(l)                                  # propagates this literal with no reason (this is a decision)

        self._cancelUntil(0) # Notes that if SAT was proved, no cancelUntil will be called and thus all variables keep their assigned values
        return self._cst.lit_Undef
            
    def solve(self, maxConflicts = None):
        '''The solve repeatedly call the search function. Each time a restart is fired,
           the search function returns lit_Undef'''
        self._time1 = time.time()
        try:
            self._status = self._cst.lit_Undef
            self._restarts = 0
            while self._status == self._cst.lit_Undef:
                self._restarts += 1
                self._status = self._search(None if maxConflicts==None else maxConflicts(self)) 
        except KeyboardInterrupt:
            self._searchTime = time.time() - self._time1
            print("c Interrupted")
            self.printFinalStats()
            return 1 

        self._searchTime = time.time() - self._time1
        return self._status 


    def printFinalStats(self):
        if self._conflicts == 0:
            print("c conflicts: 0")
            return
        print("c cpu time: \033[1;32m{t:03.2f}\033[0ms (search={ts:03.2f}s)".format(t=time.time()-self._time0, ts=self._searchTime)) 
        print("c conflicts: " + str(self._conflicts) + " (" + str(int(self._conflicts /self._searchTime)) + "/s)")
        print("c unary clauses:" + str(self._unaryClauses))
        print("c restarts: " + str(self._restarts))
        print("c propagations: " + str(self._propagations) + " (" + str(int(self._propagations / self._searchTime)) + "/s)")
        print("c Moved Watches: " + str(self._propMoves))
        print("c Inspected Watches: " + str(self._watchesInspections))
        print("c Avg Decision Levels: " + str(int(self._sumDecisionLevel / self._conflicts)))
        print("c Resolutions: {r:d} ({rc:03.2f}/confl)".format(r=self._resolutions, rc=self._resolutions/self._conflicts))


# when running as a solver:
# 1- Print the banner
# 2- Read the CNF
# 3- Push all the clauses to a new solver
# 4- Solve it (with a restart strategy)
# 5- Interpret the result

if __name__ == "__main__":

    def printUsage():
       print("pysat solver: learning clause learning algorithms (slowly learning things).")

    def banner():
        # The banner (a mandatory thing for students to play with)
        _thisispysat = '''
   ___         ____ ___  ______
  / _ \ __ __ / __// _ |/_  __/
 / ___// // /_\ \ / __ | / /   
/_/    \_, //___//_/ |_|/_/    
      /___/                    
'''
        print('\n'.join([ 'c \033[1;31m' + line + '\033[0m' for line in _thisispysat.split('\n')]))
        print("c                               \033[1;33mThis is pysat 0.2 (L. Simon 2016-2018)\033[0m\nc")
        print("c (slowly) learning CDCL algorithms (roughly 10-50x slower than plain C/C++ CDCL implementations)")
        print("c          but this is a native Python implementation. Easy to play with!")
    

    def readFile(solver, filename):
        ''' A very python-like parser for CNF files (probably too nested I fear)'''
        starttime = time.time()
        print("c Opening file {f:s}".format(f=filename))
    
        for line in myopen(filename):
            if not line[0] in ['c','p']:
                solver.addClause([l for l in list(map(int,line.split())) if l is not 0]) 

        print("c File readed in {t:03.2f}s".format(t=time.time()-starttime))

    banner()
    solver = Solver()
    cst = Constants()

    if len(sys.argv) > 1:
        readFile(solver, sys.argv[1])
        solver.buildDataStructure()
    else:
        printUsage()
        sys.exit(1)

    result = solver.solve(maxConflicts = lambda s: int((100*(1.5**s._restarts))))

    if result == cst.lit_False:
        print("c UNSATISFIABLE")
    elif result == cst.lit_True:
        print("c SATISFIABLE")
    else:
        print("c UNKNOWN")
    solver.printFinalStats()

    if result == cst.lit_True and solver._config.printModel: # SAT was claimed
        #print("v ", end="")
        for v in range(0, len(solver._values)):
           val = solver._values[v]
           assert val is not cst.lit_Undef
           solver._finalModel.append(val==cst.lit_True)
           if val==cst.lit_False: print("-")#, end="")
           print(str(v+1)+ " ")#, end="")
        print("")

    # As in the SAT competition, ends with the correct error code
    if result == cst.lit_False:
       sys.exit(20)
    if result == cst.lit_True:
       sys.exit(10)


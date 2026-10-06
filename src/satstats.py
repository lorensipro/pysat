import time

class Stats():
    ''' Statistics of a solver, kept outside of the solver itself.

        Each solver declares the counters it needs (addCounter) and the averages
        it wants to see at the end (addAverage). Counters are simple attributes,
        the solver just increments them: self._stats.conflicts += 1
        In the hot loops (propagation), take a local copy first: stats = self._stats '''

    def __init__(self):
        self._time0 = time.time()      # creation time (the solver was built just after)
        self._time1 = None             # beginning of the search
        self.searchTime = 0.0          # time spent in the search (updated by stopSearch)
        self._lines = []               # what printFinal prints, in the order of the declarations

    def addCounter(self, name, label = None, rate = None):
        ''' Adds a counter, initialized to 0. If a label is given, the counter is printed by printFinal.
            rate is None, 'time' (prints the number per second) or the name of another counter
            (prints the number per unit of this other counter) '''
        setattr(self, name, 0)
        if label is not None: self._lines.append((label, name, rate, False))

    def addAverage(self, label, name, perName):
        ''' Prints at the end the (integer) average of the counter name per unit of the counter perName '''
        self._lines.append((label, name, perName, True))

    def startSearch(self):
        self._time1 = time.time()

    def stopSearch(self):
        self.searchTime = time.time() - self._time1

    def printFinal(self):
        print("c cpu time: \033[1;32m{t:03.2f}\033[0ms (search={ts:03.2f}s)".format(t=time.time()-self._time0, ts=self.searchTime))
        for label, name, rate, isAverage in self._lines:
            value = getattr(self, name)
            if isAverage:
                per = getattr(self, rate)
                if per > 0: print("c {l:s}: {a:d}".format(l=label, a=int(value / per)))
            elif rate is None:
                print("c {l:s}: {v:d}".format(l=label, v=value))
            elif rate == 'time':
                print("c {l:s}: {v:d} ({r:d}/s)".format(l=label, v=value, r=int(value / max(self.searchTime, 1e-6))))
            else:
                per = getattr(self, rate)
                print("c {l:s}: {v:d} ({r:03.2f}/{n:s})".format(l=label, v=value, r=value / max(per, 1), n=rate))

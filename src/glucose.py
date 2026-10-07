from minimize import *
from vmtf import VMTF
from satboundedqueue import SatBoundedQueue

class Glucose(Minimize):
    ''' CDCL with the dynamic restarts of Glucose (Audemard and Simon 2009, 2012), driven by the LBD.

        Restart when the recent learnt clauses are worse than usual: when the average LBD of the last 50
        conflicts, multiplied by K = 0.8, is larger than the average LBD of all the conflicts. After a
        restart, the queue of the last LBD is emptied: the next restart waits for at least 50 conflicts.

        Blocking restarts (Glucose 2.1, 2012): when the assignment at the conflict is much larger than usual
        (R = 1.4 times the average size of the last 5000 conflicts), the solver may be near a model: the queue
        of the LBD is emptied, which postpones the next restart.

        The statistics are updated after each conflict (_afterConflict), the decision to restart is taken
        before the next decision (_restartNeeded).'''

    class Configuration(Minimize.Configuration):
        ''' Contains all the configuration variables for the solver '''
        restarts = 'glucose'           # 'none', 'geometric', 'luby' (see Restarts) or 'glucose'
        lbdQueueSize = 50              # Glucose values
        restartK = 0.8
        blocking = True                # Blocking restarts (Glucose 2.1)
        trailQueueSize = 5000
        blockingR = 1.4
        blockingStart = 10000          # No blocking before 10000 conflicts

    def __init__(self):
        super().__init__()
        self._lbdQueue = SatBoundedQueue(self._config.lbdQueueSize)        # The LBD of the last conflicts
        self._trailQueue = SatBoundedQueue(self._config.trailQueueSize)    # The sizes of the assignment at the last conflicts

        self._stats.addCounter('blockedRestarts', "Blocked restarts")
        return

    def _afterConflict(self, learnt, trailSize):
        super()._afterConflict(learnt, trailSize)
        if self._config.restarts != 'glucose': return
        if (self._config.blocking and self._stats.conflicts > self._config.blockingStart and self._lbdQueue.isValid()
                and self._trailQueue.isValid() and trailSize > self._config.blockingR * self._trailQueue.getAvg()):
            self._lbdQueue.fastClear()                             # A much larger assignment than usual: no restart now
            self._stats.blockedRestarts += 1
        self._trailQueue.append(trailSize)
        self._lbdQueue.append(learnt.lbd)

    def _restartNeeded(self):
        if self._config.restarts != 'glucose': return super()._restartNeeded()
        if not self._lbdQueue.isValid(): return False              # Less than 50 conflicts since the last restart
        if self._lbdQueue.getAvg() * self._config.restartK <= self._stats.sumLBD / self._stats.conflicts: return False
        self._lbdQueue.fastClear()
        self._stats.restarts += 1
        return True


class GlucoseVMTF(VMTF, Glucose):
    ''' The Glucose restarts with VMTF instead of VSIDS: close to the focused mode of CaDiCaL and Kissat (VMTF, and
        restarts driven by the LBD). Nothing to write, as for MinimizeVMTF: multiple inheritance.'''


if __name__ == "__main__":
    runFromCommandLine(GlucoseVMTF if '--vmtf' in sys.argv else Glucose, "Glucose")

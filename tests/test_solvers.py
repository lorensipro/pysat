''' Tests for the CDCL (pysat.py) and DPLL (pysatdpll.py) solvers.

    Run them from the root of the repository with:
        python -m unittest discover tests
'''

import os, sys, random, itertools, subprocess, tempfile, unittest

SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src')
EXAMPLES = os.path.join(SRC, '..', 'examples')
sys.path.insert(0, SRC)

import pysat, pysatdpll, dpll, cdcl, sato, watches, vsids, lookahead
from satutils import readFile


def randomFormula(rnd, n, m, k=3):
    ''' A random k-CNF with n variables and m clauses (as in genRandom.py) '''
    clauses = []
    for nc in range(0,m):
        c = []
        while len(c) < k:
            l = rnd.randint(1,n) * (1 if rnd.randint(0,1) else -1)
            if not l in c and not -l in c: c.append(l)
        clauses.append(c)
    return clauses

def bruteForceSat(clauses, n):
    ''' Checks the satisfiability by enumerating all the 2^n assignments '''
    for values in itertools.product([False, True], repeat=n):
        if all(any(values[abs(l)-1] == (l > 0) for l in c) for c in clauses): return True
    return False

def isModel(clauses, model):
    ''' Checks that the model satisfies all the clauses '''
    trueLits = set(model)
    return all(any(l in trueLits for l in c) for c in clauses)

def runSolver(solverClass, clauses):
    ''' Builds a quiet solver of the given class, solves the clauses and returns the solver and the result '''
    solver = solverClass()
    solver._config.verbosity = 0
    for c in clauses: solver.addClause(c)
    if hasattr(solver, 'buildDataStructure'): solver.buildDataStructure() # (old solvers, not incremental)
    return solver, solver.solve()


class SolverTests():
    ''' Tests shared by all the solvers (the class to test is in self.solverClass) '''

    def checkFormula(self, clauses, n, expectedSat=None):
        if expectedSat is None: expectedSat = bruteForceSat(clauses, n)
        solver, result = runSolver(self.solverClass, clauses)
        cst = solver._cst
        if expectedSat:
            self.assertEqual(result, cst.lit_True, "should be SAT: " + str(clauses))
            self.assertTrue(isModel(clauses, solver.finalModel), "wrong model for: " + str(clauses))
        else:
            self.assertEqual(result, cst.lit_False, "should be UNSAT: " + str(clauses))

    def test_randomSmallFormulas(self):
        rnd = random.Random(2026)
        for i in range(300):
            n = rnd.randint(3,10)
            m = int(n * rnd.uniform(2.0, 6.0))
            self.checkFormula(randomFormula(rnd, n, m), n)

    def test_randomMixedSizes(self):
        rnd = random.Random(42)
        for i in range(200):
            n = rnd.randint(2,8)
            clauses = randomFormula(rnd, n, rnd.randint(1,4*n), k=1) if i % 10 == 0 else []
            clauses += [c for k in (2,3,4) for c in randomFormula(rnd, n, rnd.randint(0,2*n), k=min(k,n))]
            self.checkFormula(clauses, n)

    def test_sample(self):
        clauses = []
        class Reader():
            def addClause(self, c): clauses.append(c)
        readFile(Reader(), os.path.join(EXAMPLES, 'sample.cnf'), verbosity=0)
        self.assertEqual(len(clauses), 17)
        self.checkFormula(clauses, 7, expectedSat=False)

    def test_emptyFormula(self):
        self.checkFormula([], 0, expectedSat=True)

    def test_emptyClause(self):
        self.checkFormula([[1, 2], []], 2, expectedSat=False)

    def test_oppositeUnaryClauses(self):
        self.checkFormula([[1, 2], [3], [-3]], 3, expectedSat=False)

    def test_duplicatedUnaryClauses(self):
        self.checkFormula([[1], [1], [-1, 2]], 2, expectedSat=True)

    def test_duplicatedLiteralsAndTautologies(self):
        self.checkFormula([[1, 1, 2], [-1, -1], [2, -2, 3], [-2, 3, 3]], 3, expectedSat=True)
        self.checkFormula([[1, 1], [-1, -1, -1]], 1, expectedSat=False)


class CDCLTests(SolverTests, unittest.TestCase):
    solverClass = pysat.Solver

class DPLLTests(SolverTests, unittest.TestCase):
    solverClass = pysatdpll.Solver

class IncrementalTests():
    ''' Tests for the incremental solvers: clauses are added between two calls to solve() '''

    def test_incremental(self):
        rnd = random.Random(1789)
        for i in range(100):
            n = rnd.randint(3,9)
            solver = self.solverClass()
            solver._config.verbosity = 0
            clauses = []
            for step in range(6):                                  # The formula gets stronger at each step
                for c in randomFormula(rnd, n, rnd.randint(1, n), k=rnd.choice([1,2,3,3])):
                    clauses.append(c); solver.addClause(c)
                result = solver.solve()
                if bruteForceSat(clauses, n):
                    self.assertEqual(result, solver._cst.lit_True, "should be SAT: " + str(clauses))
                    self.assertTrue(isModel(clauses, solver.finalModel))
                else:
                    self.assertEqual(result, solver._cst.lit_False, "should be UNSAT: " + str(clauses))

class ChainDPLLTests(SolverTests, IncrementalTests, unittest.TestCase):
    solverClass = dpll.DPLL

class ChainCDCLTests(SolverTests, IncrementalTests, unittest.TestCase):
    solverClass = cdcl.CDCL

class ChainSATOTests(SolverTests, IncrementalTests, unittest.TestCase):
    solverClass = sato.SATO

class ChainWatchesTests(SolverTests, IncrementalTests, unittest.TestCase):
    solverClass = watches.Watches

class ChainVSIDSTests(SolverTests, IncrementalTests, unittest.TestCase):
    solverClass = vsids.VSIDS

class BalancedDPLL(dpll.DPLL):
    class Configuration(dpll.DPLL.Configuration):
        heuristic = 'balanced'

class BalancedDPLLTests(SolverTests, IncrementalTests, unittest.TestCase):
    solverClass = BalancedDPLL

class LookaheadTests(SolverTests, IncrementalTests, unittest.TestCase):
    solverClass = lookahead.Lookahead

class DoubleLookaheadTests(SolverTests, IncrementalTests, unittest.TestCase):
    solverClass = lookahead.DoubleLookahead


class ParserTests(unittest.TestCase):

    def readString(self, content):
        clauses = []
        class Reader():
            def addClause(self, c): clauses.append(c)
        with tempfile.NamedTemporaryFile('w', suffix='.cnf', delete=False) as f:
            f.write(content)
        try:
            readFile(Reader(), f.name, verbosity=0)
        finally:
            os.remove(f.name)
        return clauses

    def test_dimacsVariants(self):
        # comments, empty lines, clauses on several lines, several clauses on a line, SATLIB '%' end marker
        content = "c comment\np cnf 4 4\n\n1 -2 0 3\n 4 0\n  -1\n-3 0\n2 0\n%\n0\n"
        self.assertEqual(self.readString(content), [[1, -2], [3, 4], [-1, -3], [2]])

    def test_lastClauseWithoutZero(self):
        self.assertEqual(self.readString("p cnf 2 2\n1 2 0\n-1 -2\n"), [[1, 2], [-1, -2]])


class CommandLineTests(unittest.TestCase):
    ''' Runs the solvers as scripts, as in the SAT competitions (exit code 10 = SAT, 20 = UNSAT) '''

    def run_(self, script, cnf):
        return subprocess.run([sys.executable, os.path.join(SRC, script), cnf], capture_output=True, text=True)

    def test_unsatBenchmarks(self):
        for script in ['pysat.py', 'pysatdpll.py', 'dpll.py', 'cdcl.py', 'sato.py', 'watches.py', 'vsids.py', 'lookahead.py']:
            for f in ['sample.cnf', os.path.join('BMC-Unsat', 'barrel2.cnf.gz'), os.path.join('BMC-Unsat', 'longmult0.cnf.gz')]:
                r = self.run_(script, os.path.join(EXAMPLES, f))
                self.assertEqual(r.returncode, 20, script + " " + f + "\n" + r.stdout + r.stderr)
                self.assertIn("s UNSATISFIABLE", r.stdout)

    def test_satModelLine(self):
        clauses = randomFormula(random.Random(7), 30, 90)
        with tempfile.NamedTemporaryFile('w', suffix='.cnf', delete=False) as f:
            f.write("p cnf 30 90\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses))
        try:
            for script in ['pysat.py', 'pysatdpll.py', 'dpll.py', 'cdcl.py', 'sato.py', 'watches.py', 'vsids.py', 'lookahead.py']:
                r = self.run_(script, f.name)
                self.assertEqual(r.returncode, 10, r.stdout + r.stderr)
                model = [int(x) for line in r.stdout.splitlines() if line.startswith('v') for x in line[1:].split()]
                self.assertEqual(model[-1], 0)
                self.assertTrue(isModel(clauses, model[:-1]))
        finally:
            os.remove(f.name)


if __name__ == "__main__":
    unittest.main()

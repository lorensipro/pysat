# pysat — a CDCL SAT solver in pure Python #

This is a CDCL Python (3.9+) native implementation. It is very slow (like 10x-50x times) but the data structure is a native python one, made with as many tricks as possible.
It is a nice toy to play with. No dependency, only the Python standard library.

Not to be confused with [PySAT](https://pysathq.github.io/) (`pip install python-sat`), the Python toolkit that wraps C/C++ SAT solvers.

### Learn Clause Learning Algorithms ###

The idea is to be able to quickly play with CDCL concepts.
If you understand it, you can dig into Minisat/Glucose source code now!

The CDCL solver (`src/pysat.py`) implements:

* 2-watched literals propagation,
* conflict analysis with the first UIP scheme,
* VSIDS heuristics (with a heap of variables, as in Minisat) and phase saving,
* geometric restarts.

A plain DPLL solver (`src/pysatdpll.py`) is also given, written with the same data structures and function names, to compare both algorithms: occurrence lists, static heuristics and chronological backtracking, no learning.

### How to use it? ###

Just go into the src directory and type:

```
python pysat.py ../examples/sample.cnf
python pysatdpll.py ../examples/sample.cnf
```

Input files are in the DIMACS CNF format, possibly compressed (`.cnf.gz`). As in the SAT competitions, the solver prints `s SATISFIABLE` (with the model on the `v` line) or `s UNSATISFIABLE`, and exits with code 10 or 20.

Random formulas can be generated with:

```
python genRandom.py 100 3 4.26 > random.cnf    # 100 variables, 3-CNF, ratio 4.26 (optional 4th argument: seed)
```

Some benchmarks are available in `examples/BMC-Unsat` (try `barrel5.cnf.gz`, it takes a few seconds).

The solver can also be used from Python:

```python
from pysat import Solver

s = Solver()
s.addClause([1, -2])
s.addClause([2, 3])
s.buildDataStructure()
if s.solve() == s._cst.lit_True:
    print(s.finalModel)
```

### Tests ###

From the root of the repository:

```
python -m unittest discover tests
```

Both solvers are checked against a brute-force enumeration on random formulas, and the models are verified.

Good luck!

''' The experiments of the pysat chain of solvers, to replay the tables shown in the course.

    Usage:
        python experiments.py                       # all the experiments
        python experiments.py heuristics restarts   # only some of them
        python experiments.py --list                # the available experiments
        options: --timeout 60 (seconds per run)  --python python3 (interpreter used for the runs)
                 --jobs 4 (number of runs in parallel; default 1. Parallel runs share the memory and the
                 caches, and some cores may be slower: the times are less precise, the counters are the same)

    Each run is a separate process (python -O, no assertions), killed after the timeout.
    The results are printed as Markdown tables and saved in experiments/results/<name>.md and .jsonl.
    The recent benchmarks are downloaded from GBD if needed (examples/fetch_gbd.py), the random ones
    are generated again from their seeds (src/genRandom.py), in experiments/random/.
'''

import os, sys, json, time, subprocess, importlib
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, '..', 'src')
EXAMPLES = os.path.join(HERE, '..', 'examples')
RANDOM = os.path.join(HERE, 'random')
RESULTS = os.path.join(HERE, 'results')

# The solvers: name -> (module, class, configuration changes)
SOLVERS = {
    'dpll-freq':      ('dpll', 'DPLL', {}),
    'dpll-balanced':  ('dpll', 'DPLL', {'heuristic': 'balanced'}),
    'lookahead':      ('lookahead', 'Lookahead', {}),
    'double':         ('lookahead', 'DoubleLookahead', {}),
    'cdcl':           ('cdcl', 'CDCL', {}),
    'sato':           ('sato', 'SATO', {}),
    'watches':        ('watches', 'Watches', {}),
    'vsids':          ('vsids', 'VSIDS', {}),
    'vsids-occ':      ('vsids', 'VSIDS', {'initialActivity': 'occurrences'}),
    'luby':           ('restarts', 'Restarts', {'phaseSaving': False}),
    'geometric':      ('restarts', 'Restarts', {'restarts': 'geometric', 'phaseSaving': False}),
    'phase':          ('restarts', 'Restarts', {'restarts': 'none'}),
    'luby+phase':     ('restarts', 'Restarts', {}),
    'reduce-activity': ('reduce', 'Reduce', {'reduce': 'activity'}),
    'reduce-lbd':     ('reduce', 'Reduce', {}),
    'min-local':      ('minimize', 'Minimize', {'minimize': 'local'}),
    'min-recursive':  ('minimize', 'Minimize', {}),
}

# Random 3-SAT at the threshold (ratio 4.26), UNSAT: (variables, seed) for src/genRandom.py
RANDOM_UNSAT = [(50, 3), (75, 9), (100, 19), (125, 100), (125, 101), (150, 102), (150, 103), (175, 104), (175, 107)]

def bmc(*names): return [os.path.join(EXAMPLES, 'BMC-Unsat', n + '.cnf.gz') for n in names]
def rnd(): return [randomInstance(n, seed) for n, seed in RANDOM_UNSAT]
def recent(*names):
    ''' The recent instances (GBD), by the end of their file names (all of them if no name) '''
    sys.path.insert(0, EXAMPLES)
    import fetch_gbd
    fetch_gbd.fetch()
    files = sorted(os.listdir(fetch_gbd.DEST))
    return [os.path.join(fetch_gbd.DEST, f) for f in files if not names or any(f.endswith(n) for n in names)]

FEASIBLE_RECENT = ['3col120_5_2.shuffled.cnf.xz', 'Steiner-27-10-bce.cnf.xz', 'c499_gr_2pin_w6.shuffled.cnf.xz',
                   'connm-ue-csp-sat-n600-d-0.02-s1022905465.used-as.sat04-951.cnf.xz', 'x9-06099.sat.sanitized.cnf.xz',
                   'Wallace_Bits_Fast_2.cnf.cnf.xz', 'ferry8_ks99i.renamed-as.sat05-4005.cnf.xz', 'iso-brn100.shuffled-as.sat05-3025.cnf.xz',
                   'Break_08_24.xml.cnf.xz', 'Break_unsat_06_07.xml.cnf.xz']

# The experiments: name -> (title, solvers, function giving the instances, columns)
EXPERIMENTS = {
    'propagation': ("Propagation: counters, head/tail (SATO), watched literals (same search)",
                    ['cdcl', 'sato', 'watches'],
                    lambda: bmc('barrel4', 'barrel5', 'longmult4', 'longmult5', 'queueinvar6', 'queueinvar8', 'queueinvar10'),
                    ['time', 'conflicts', 'propagations', 'clauseVisits', 'clauseRestores', 'pointerMoves']),
    'heuristics': ("DPLL: trying or thinking (static heuristics, lookahead, double lookahead), CDCL as reference",
                   ['dpll-freq', 'dpll-balanced', 'lookahead', 'double', 'watches', 'vsids'],
                   lambda: rnd() + bmc('barrel4', 'barrel5', 'queueinvar6', 'queueinvar10', 'longmult4', 'longmult5'),
                   ['time', 'decisions', 'conflicts', 'propagations', 'failedLiterals']),
    'restarts': ("VSIDS, restarts and phase saving",
                 ['watches', 'vsids', 'vsids-occ', 'phase', 'geometric', 'luby', 'luby+phase'],
                 lambda: bmc('barrel5', 'barrel6', 'longmult6', 'queueinvar14') + recent(*FEASIBLE_RECENT) + rnd()[-2:],
                 ['time', 'conflicts', 'decisions', 'restarts']),
    'reduce': ("Reduction of the learnt clauses: none, by activity (Minisat), by LBD (Glucose)",
               ['luby+phase', 'reduce-activity', 'reduce-lbd'],
               lambda: bmc('barrel6', 'barrel7', 'longmult6', 'longmult7', 'queueinvar16') + recent('ferry8_ks99i.renamed-as.sat05-4005.cnf.xz',
                   'Break_unsat_06_07.xml.cnf.xz', 'x9-06099.sat.sanitized.cnf.xz', '3col120_5_2.shuffled.cnf.xz') + rnd()[-2:],
               ['time', 'conflicts', 'removedClauses', 'propagations', 'clauseVisits']),
    'minimize': ("Minimization of the learnt clauses: none, local, recursive (Minisat 2)",
                 ['reduce-lbd', 'min-local', 'min-recursive'],
                 lambda: bmc('barrel6', 'barrel7', 'longmult6', 'longmult7', 'queueinvar16') + recent('ferry8_ks99i.renamed-as.sat05-4005.cnf.xz',
                     'Break_unsat_06_07.xml.cnf.xz', 'x9-06099.sat.sanitized.cnf.xz', '3col120_5_2.shuffled.cnf.xz') + rnd()[-2:],
                 ['time', 'conflicts', 'sumLearntSize', 'minimizedLits', 'propagations']),
    'recent': ("Recent benchmarks (SAT competitions 2020-2025, from GBD)",
               ['watches', 'vsids', 'luby+phase'],
               lambda: recent(),
               ['time', 'conflicts']),
}


def randomInstance(n, seed):
    ''' Generates again the random instance (if needed) '''
    os.makedirs(RANDOM, exist_ok=True)
    path = os.path.join(RANDOM, 'r%d-%d.cnf' % (n, seed))
    if not os.path.exists(path):
        cnf = subprocess.run([sys.executable, os.path.join(SRC, 'genRandom.py'), str(n), '3', '4.26', str(seed)],
                             capture_output=True, text=True, check=True).stdout
        open(path, 'w').write(cnf)
    return path

def runOne(solverName, path):
    ''' Runs one solver on one instance (in this process) and prints its statistics as JSON '''
    sys.path.insert(0, SRC)
    from satutils import readFile
    moduleName, className, changes = SOLVERS[solverName]
    solverClass = getattr(importlib.import_module(moduleName), className)
    solver = solverClass()
    for k, v in changes.items(): setattr(solver._config, k, v)
    solver._config.verbosity = 0
    readFile(solver, path, 0)
    t = time.time()
    result = solver.solve()
    stats = {k: v for k, v in vars(solver._stats).items() if not k.startswith('_') and isinstance(v, (int, float))}
    stats.update(time=round(time.time() - t, 3), result={0: 'UNSAT', 1: 'SAT'}.get(result, 'UNKNOWN'))
    print(json.dumps(stats))

def runProcess(python, timeout, solverName, path):
    ''' Runs one solver on one instance in a separate process. Returns the statistics (a dict) '''
    try:
        r = subprocess.run([python, '-O', os.path.abspath(__file__), '--one', solverName, path],
                           capture_output=True, text=True, timeout=timeout)
        d = json.loads(r.stdout)
    except subprocess.TimeoutExpired:
        d = dict(result='TIMEOUT')
    d.update(instance=os.path.basename(path), solver=solverName)
    return d

def run(name, python, timeout, jobs):
    title, solvers, instances, columns = EXPERIMENTS[name]
    os.makedirs(RESULTS, exist_ok=True)
    lines = ["## " + title, "", "Timeout: {t:d}s per run, {j:d} run(s) in parallel. Columns: {c:s}.".format(t=timeout, j=jobs, c=", ".join(columns)), ""]
    lines += ["| instance | " + " | ".join(solvers) + " |", "|---" * (len(solvers) + 1) + "|"]
    print("\n".join(lines), flush=True)
    paths = instances()
    with ThreadPoolExecutor(max_workers=jobs) as pool, open(os.path.join(RESULTS, name + '.jsonl'), 'w') as out:
        futures = {(path, s): pool.submit(runProcess, python, timeout, s, path) for path in paths for s in solvers}
        for path in paths:                                     # The lines are printed in order, as soon as they are complete
            cells = []
            for s in solvers:
                d = futures[(path, s)].result()
                out.write(json.dumps(d) + "\n"); out.flush()
                cells.append('>' + str(timeout) + 's' if d['result'] == 'TIMEOUT' else " / ".join(str(d.get(c, '-')) for c in columns))
            line = "| " + os.path.basename(path) + " | " + " | ".join(cells) + " |"
            print(line, flush=True); lines.append(line)
    open(os.path.join(RESULTS, name + '.md'), 'w').write("\n".join(lines) + "\n")


if __name__ == "__main__":
    args = sys.argv[1:]
    if args[:1] == ['--one']:
        runOne(args[1], args[2])
        sys.exit(0)
    if '--list' in args:
        for name, e in EXPERIMENTS.items(): print("{n:12s} {t:s}".format(n=name, t=e[0]))
        sys.exit(0)
    timeout = 60; python = sys.executable; jobs = 1; names = []
    i = 0
    while i < len(args):
        if args[i] == '--timeout': timeout = int(args[i+1]); i += 2
        elif args[i] == '--python': python = args[i+1]; i += 2
        elif args[i] == '--jobs': jobs = int(args[i+1]); i += 2
        else: names.append(args[i]); i += 1
    for name in names or list(EXPERIMENTS):
        run(name, python, timeout, jobs)
        print()

''' Generates the source browser of the pysat chain of solvers: docs/index.html (published by GitHub Pages).

    Each class of the chain is a node of the inheritance tree. For each node, the page shows what the
    class changes: its redefined methods as a diff with the version of its parent, its new methods,
    its options and counters, the hooks it leaves to its descendants, the whole solver at this step,
    and the measures of the experiments (experiments/results/*.jsonl).

    Usage: python tools/navigateur.py        (run it again after any change in src/)
'''

import os, sys, io, ast, json, html, inspect, keyword, difflib, tokenize, textwrap, importlib.util

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')
SRC = os.path.join(ROOT, 'src')
OUT = os.path.join(ROOT, 'docs', 'index.html')
sys.path.insert(0, SRC)

# The classes of the chain, in reading order: (module, class)
CHAIN = [('satsolver', 'Solver'), ('dpll', 'DPLL'), ('cdcl', 'CDCL'), ('sato', 'SATO'), ('watches', 'Watches'),
         ('vsids', 'VSIDS'), ('restarts', 'Restarts'), ('reduce', 'Reduce'), ('minimize', 'Minimize'),
         ('lookahead', 'Lookahead'), ('lookahead', 'DoubleLookahead')]

# One line per class, for the tree of the page: (French, English)
SUMMARIES = {
    'Solver': ("la racine : la formule, l'API, les statistiques", "the root: the formula, the API, the statistics"),
    'DPLL': ("propager, décider, revenir en arrière (1962)", "propagate, decide, backtrack (1962)"),
    'CDCL': ("apprendre une clause à chaque conflit (GRASP, 1996)", "learn a clause at each conflict (GRASP, 1996)"),
    'SATO': ("propager avec deux pointeurs tête/queue (1997)", "propagate with head/tail pointers (1997)"),
    'Watches': ("deux littéraux surveillés, rien à défaire (Chaff, 2001)", "two watched literals, nothing to undo (Chaff, 2001)"),
    'VSIDS': ("choisir les variables des conflits récents (Chaff, 2001)", "choose the variables of recent conflicts (Chaff, 2001)"),
    'Restarts': ("redémarrer et garder les phases (Minisat 2.2)", "restart and keep the phases (Minisat 2.2)"),
    'Reduce': ("oublier des clauses apprises, par LBD (Glucose, 2009)", "forget learnt clauses, by LBD (Glucose, 2009)"),
    'Minimize': ("raccourcir les clauses apprises (Minisat 2)", "shorten the learnt clauses (Minisat 2)"),
    'Lookahead': ("réfléchir avant de choisir : essayer chaque variable", "think before choosing: try each variable"),
    'DoubleLookahead': ("réfléchir encore plus : un second niveau", "think even more: a second level"),
}

# The titles of the experiments: (French, English)
TITLES = {
    'propagation': ("Propager : compteurs, pointeurs tête/queue (SATO), littéraux surveillés (même recherche)",
                    "Propagation: counters, head/tail pointers (SATO), watched literals (same search)"),
    'heuristics': ("DPLL : essayer ou réfléchir (heuristiques statiques, lookahead, double lookahead), CDCL en référence",
                   "DPLL: trying or thinking (static heuristics, lookahead, double lookahead), CDCL as reference"),
    'restarts': ("VSIDS, redémarrages et sauvegarde de phase", "VSIDS, restarts and phase saving"),
    'reduce': ("Réduction des clauses apprises : aucune, par activité (Minisat), par LBD (Glucose)",
               "Reduction of the learnt clauses: none, by activity (Minisat), by LBD (Glucose)"),
    'minimize': ("Minimisation des clauses apprises : aucune, locale, récursive (Minisat 2)",
                 "Minimization of the learnt clauses: none, local, recursive (Minisat 2)"),
    'recent': ("Instances récentes (compétitions SAT 2020-2025, base GBD)", "Recent instances (SAT competitions 2020-2025, GBD)"),
}

# Columns of the measures: (key, French, English)
COLUMNS = [('time', 'temps (s)', 'time (s)'), ('conflicts', 'conflits', 'conflicts'), ('decisions', 'décisions', 'decisions'),
           ('propagations', 'propagations', 'propagations'), ('clauseVisits', 'clauses visitées', 'clauses visited'),
           ('clauseRestores', 'clauses restaurées', 'clauses restored'), ('sumLearntSize', 'littéraux appris', 'learnt literals'),
           ('removedClauses', 'clauses retirées', 'removed clauses'), ('failedLiterals', 'failed literals', 'failed literals')]


def highlight(source):
    ''' Python source -> list of lines of HTML, with <span class="..."> for keywords, strings, comments... '''
    starts = [0]
    for line in source.splitlines(True): starts.append(starts[-1] + len(line))
    offset = lambda rc: starts[rc[0] - 1] + rc[1]
    out = []; last = 0; previous = None
    try:
        for tok in tokenize.generate_tokens(io.StringIO(source).readline):
            if tok.type == tokenize.ENDMARKER: break
            start, end = offset(tok.start), offset(tok.end)
            if start < last: continue
            out.append(html.escape(source[last:start]))
            cls = None
            if tok.type == tokenize.COMMENT: cls = 'com'
            elif tok.type == tokenize.STRING: cls = 'str'
            elif tok.type == tokenize.NUMBER: cls = 'num'
            elif tok.type == tokenize.NAME:
                if keyword.iskeyword(tok.string): cls = 'kw'
                elif tok.string in ('self', 'super'): cls = 'self'
                elif previous in ('def', 'class'): cls = 'fn'
                previous = tok.string
            text = html.escape(source[start:end])
            if cls: text = '\n'.join('<span class="%s">%s</span>' % (cls, part) if part else '' for part in text.split('\n'))
            out.append(text)
            last = end
    except (tokenize.TokenError, IndentationError, SyntaxError):
        return [html.escape(l) for l in source.splitlines()]
    out.append(html.escape(source[last:]))
    lines = ''.join(out).split('\n')
    while lines and lines[-1] == '': lines.pop()
    return lines

def sourceOf(obj):
    return textwrap.dedent(inspect.getsource(obj)).rstrip('\n')

def origin(cls, name):
    ''' The class (in the MRO of cls) that defines the method name '''
    for c in cls.__mro__:
        if name in c.__dict__: return c
    return None

def isHook(func):
    ''' A method that does nothing (a docstring and at most a trivial return): a hook for the descendants '''
    body = ast.parse(sourceOf(func)).body[0].body
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant): body = body[1:]   # (the docstring)
    return len(body) <= 1 and all(isinstance(st, ast.Raise) or isinstance(st, ast.Return) and (st.value is None or isinstance(st.value, (ast.Constant, ast.Name)))
                                  for st in body)

def docLines(source):
    ''' The indices of the lines of the docstring of the (only) function of source '''
    body = ast.parse(source).body[0].body
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
        return set(range(body[0].lineno - 1, body[0].end_lineno))
    return set()

def diffLines(old, new):
    ''' Full listing of new, with the lines removed from old: [[tag, html, isDoc], ...], tag in ' ', '+', '-' '''
    oldRaw, newRaw = old.splitlines(), new.splitlines()
    oldHl, newHl = highlight(old), highlight(new)
    if len(oldHl) != len(oldRaw): oldHl = [html.escape(l) for l in oldRaw]
    if len(newHl) != len(newRaw): newHl = [html.escape(l) for l in newRaw]
    oldDoc, newDoc = docLines(old), docLines(new)
    result = []
    for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, oldRaw, newRaw, autojunk=False).get_opcodes():
        if op == 'equal':
            result += [[' ', newHl[j], j in newDoc] for j in range(j1, j2)]
        else:
            result += [['-', oldHl[i], i in oldDoc] for i in range(i1, i2)]
            result += [['+', newHl[j], j in newDoc] for j in range(j1, j2)]
    return result

def loadExperiments():
    spec = importlib.util.spec_from_file_location('experiments', os.path.join(ROOT, 'experiments', 'experiments.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    results = {}
    for name in module.EXPERIMENTS:
        path = os.path.join(ROOT, 'experiments', 'results', name + '.jsonl')
        if os.path.exists(path):
            results[name] = [json.loads(l) for l in open(path)]
    return module, results

def measures(cls, experiments, results):
    ''' The experiments where the default configuration of cls is compared with the one of its nearest ancestor '''
    def defaultName(c):
        for name, (m, k, changes) in experiments.SOLVERS.items():
            if m == c.__module__ and k == c.__name__ and not changes: return name
        return None
    me = defaultName(cls)
    if me is None: return []
    out = []
    for exp, rows in results.items():
        title, solvers = TITLES.get(exp, (experiments.EXPERIMENTS[exp][0],) * 2), experiments.EXPERIMENTS[exp][1]
        if me not in solvers: continue
        ref = None
        for c in cls.__mro__[1:]:                                  # The nearest ancestor measured in this experiment
            n = defaultName(c)
            if n in solvers: ref = (c.__name__, n); break
        names = ([ref[1]] if ref else []) + [me]
        cols = [(k, (fr, en)) for k, fr, en in COLUMNS if any(k in r for r in rows if r['solver'] in names)]
        table = []
        for inst in dict.fromkeys(r['instance'] for r in rows):
            cells = []
            for n in names:
                r = next((r for r in rows if r['instance'] == inst and r['solver'] == n), None)
                cells.append(None if r is None else ({'timeout': True} if r['result'] == 'TIMEOUT' else {k: r.get(k) for k, _ in cols}))
            table.append({'instance': inst.split('-', 1)[1] if len(inst) > 33 and inst[32] == '-' else inst, 'cells': cells})
        out.append({'experiment': exp, 'title': title, 'reference': ref[0] if ref else None,
                    'solvers': [(ref[0] if ref else None), cls.__name__][-len(names):],
                    'columns': [label for _, label in cols], 'keys': [k for k, _ in cols], 'rows': table})
    return out

def counters(cls):
    try:
        s = cls()._stats
    except Exception:
        return []
    return [(name, label) for label, name, rate, isAverage in s._lines]

def build():
    classes = [getattr(importlib.import_module(m), k) for m, k in CHAIN]
    experiments, results = loadExperiments()
    nodes = []
    for cls in classes:
        parent = cls.__bases__[0] if cls.__bases__[0] in classes else None
        own = [(n, f) for n, f in cls.__dict__.items() if inspect.isfunction(f)]
        methods = []
        for name, func in own:
            src = sourceOf(func)
            entry = {'name': name, 'source': highlight(src), 'doc': sorted(docLines(src)), 'hook': isHook(func)}
            if parent is not None and hasattr(parent, name):
                po = origin(parent, name)
                psrc = sourceOf(getattr(parent, name))
                entry.update(kind='redefinie', parentOrigin=po.__name__, diff=diffLines(psrc, src),
                             mode='etend' if 'super(' in src or (po.__name__ + '.' + name) in src or (parent.__name__ + '.') in src else 'remplace')
            else:
                entry.update(kind='ajoutee')
            methods.append(entry)
        # The hooks left by this class: trivial methods redefined by a descendant, with the places where they are called
        hooks = []
        for name, func in own:
            if not isHook(func) or name.startswith('__'): continue
            by = [c.__name__ for c in classes if c is not cls and issubclass(c, cls) and name in c.__dict__]
            if not by: continue
            calls = [origin(c, m).__name__ + '.' + m for c in classes for m, f in c.__dict__.items()
                     if inspect.isfunction(f) and m != name and ('self.' + name + '(') in sourceOf(f)]
            hooks.append({'name': name, 'by': by, 'calls': sorted(set(calls))})
        # Options and counters, compared with the parent
        conf = cls.__dict__.get('Configuration')
        options = []
        if conf is not None:
            for k, v in vars(conf).items():
                if k.startswith('_'): continue
                old = getattr(parent.Configuration, k, '<new>') if parent is not None else '<new>'
                options.append({'name': k, 'value': repr(v), 'status': 'new' if old == '<new>' else ('changed' if old != v else 'same')})
        mine = counters(cls)
        theirs = set(n for n, _ in counters(parent)) if parent is not None else set()
        newCounters = [label for n, label in mine if n not in theirs]
        # The whole solver at this step: each method with its class of origin, in the order of the chain
        flat = []
        for c in reversed(cls.__mro__):
            if c not in classes: continue
            for name, f in c.__dict__.items():
                if inspect.isfunction(f) and origin(cls, name) is c:
                    flat.append({'name': name, 'origin': c.__name__, 'source': highlight(sourceOf(f))})
        nodes.append({'name': cls.__name__, 'parent': parent.__name__ if parent is not None else None,
                      'file': 'src/' + cls.__module__ + '.py', 'summary': SUMMARIES.get(cls.__name__, ('', '')), 'doc': inspect.cleandoc(cls.__doc__ or ''),
                      'methods': methods, 'hooks': hooks, 'options': options, 'counters': newCounters,
                      'flat': flat, 'measures': measures(cls, experiments, results)})
    page = open(os.path.join(HERE, 'navigateur.html')).read()
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    open(OUT, 'w').write(page.replace('/*DATA*/', json.dumps(nodes, ensure_ascii=False)))
    open(os.path.join(os.path.dirname(OUT), '.nojekyll'), 'w').close()  # (GitHub Pages: serve the files as they are)
    print("-> " + os.path.relpath(OUT, ROOT) + " ({n:d} classes)".format(n=len(nodes)))

if __name__ == "__main__":
    build()

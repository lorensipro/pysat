''' Generates a random k-CNF file (uniform random model, as in the SAT competitions).

    Usage: python genRandom.py [n [k [ratio [seed]]]] > file.cnf
    By default: 170 variables, 3-CNF, ratio 4.26 (the hardest point for 3-SAT)'''

import random, sys

n = int(sys.argv[1]) if len(sys.argv) > 1 else 170       # number of variables
k = int(sys.argv[2]) if len(sys.argv) > 2 else 3         # size of the clauses
ratio = float(sys.argv[3]) if len(sys.argv) > 3 else 4.26 # number of clauses / number of variables
m = int(n * ratio)

if len(sys.argv) > 4: random.seed(int(sys.argv[4]))      # Fixed seed (reproducible formulas)
else: random.seed()                                      # Uses system time

print("c Random {k:d}-CNF with {n:d} variables and ratio {r:.2f}".format(k=k, n=n, r=ratio))
print("p cnf {n:d} {m:d}".format(n=n, m=m))
for nc in range(0,m):
    c = []
    while len(c) < k:
        l = (random.randint(1,n)) * (1 if random.randint(0,1) else -1)
        if not l in c and not -l in c:                   # No duplicated literal, no tautology
            c.append(l)
    print(" ".join(str(l) for l in c) + " 0")

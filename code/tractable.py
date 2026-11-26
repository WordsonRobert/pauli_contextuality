"""Observables in <= 2 contexts: degree = # connected components (of the context graph)
that contain no observable of degree 1 and have odd total sign.  Checked against brute force."""
import numpy as np
from engine import brute_min_unsat

def degree_deg2(H, e):
    m, N = H.shape
    parent = list(range(m))
    def f(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]; i = parent[i]
        return i
    free = [False]*m
    for v in range(N):
        rs = np.nonzero(H[:, v])[0]
        if len(rs) == 1: free[rs[0]] = True
        if len(rs) == 2: parent[f(rs[0])] = f(rs[1])
    comp = {}
    for r in range(m):
        c = f(r); s, fr = comp.get(c, (0, False)); comp[c] = (s ^ int(e[r]), fr or free[r])
    return sum(1 for s, fr in comp.values() if s and not fr)

rng = np.random.default_rng(3); fails = 0
for _ in range(2000):
    m, N = int(rng.integers(2, 9)), int(rng.integers(2, 12))
    H = np.zeros((m, N), dtype=np.uint8)
    for v in range(N):
        H[rng.choice(m, int(rng.integers(1, 3)), replace=False), v] = 1
    e = rng.integers(0, 2, m).astype(np.uint8)
    fails += degree_deg2(H, e) != brute_min_unsat(H, e)
print("random degree<=2 systems: 2000 checked, failures =", fails)

"""Randomised verification of the reductions and the flip gadget."""
import sys, time
import numpy as np
from engine import degree, min_unsat, brute_min_unsat, Config
from reduction import general_hypergram, line_configuration, Builder, flip_line, triangle_split
from known import full_symplectic

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)


def random_e3(N, m):
    H = np.zeros((m, N), dtype=np.uint8)
    for j in range(m):
        H[j, rng.choice(N, 3, replace=False)] = 1
    return H, rng.integers(0, 2, m).astype(np.uint8)


# 1. general hypergrams + line configurations vs brute force
fails = 0
t0 = time.time()
for trial in range(40):
    N, m = int(rng.integers(4, 8)), int(rng.integers(4, 12))
    H0, b = random_e3(N, m)
    target = brute_min_unsat(H0, b)
    Hs, bs = triangle_split(H0, b)
    d_split, _ = min_unsat(Hs, bs)
    g = general_hypergram(H0, b)
    l = line_configuration(H0, b)
    dg, og = degree(g)
    dl, ol = degree(l)
    sizes = max(len(c) for c in l.contexts)
    ok = (target == d_split == dg == dl) and og and ol and sizes == 3
    fails += not ok
    if trial < 5 or not ok:
        print(f"N={N} m={m} min-unsat={target} split={d_split} | general: deg={dg} "
              f"({len(g.points)} pts, {g.n_qubits} qb) | lines: deg={dl} ({len(l.points)} pts, "
              f"{len(l.contexts)} lines, {l.n_qubits} qb, max ctx size {sizes}) {'OK' if ok else 'FAIL'}")
print(f"[reductions] 40 random instances, failures = {fails}  ({time.time()-t0:.0f}s)")

# 2. flip gadget on random sub-configurations of W(5,2)
W = full_symplectic(3)
fails = 0
for trial in range(30):
    k = int(rng.integers(20, 60))
    sel = sorted(rng.choice(len(W.contexts), k, replace=False))
    used = sorted({p for i in sel for p in W.contexts[i]})
    re = {p: i for i, p in enumerate(used)}
    B = Builder()
    B.nq = 3
    for p in used:
        v = W.points[p]
        B.pts.append({q: (int(v[q]), int(v[3 + q])) for q in range(3) if v[q] or v[3 + q]})
    B.ctx = [tuple(re[p] for p in W.contexts[i]) for i in sel]
    base = B.freeze()
    h_idx = int(rng.integers(len(B.ctx)))
    h = B.ctx[h_idx]
    e = np.array(base.signs, dtype=np.uint8)
    e[h_idx] ^= 1
    want, _ = min_unsat(base.incidence(), e)
    flip_line(B, h)
    got, opt = degree(B.freeze())
    fails += not (want == got and opt)
print(f"[flip gadget] 30 random W(5,2) sub-configurations, failures = {fails}")

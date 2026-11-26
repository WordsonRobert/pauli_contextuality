"""Cascade in W(7,2): orbits of transvection subgroups of Sp(8,2); witnesses: the 120 elliptic quadrics
(degree >= DQM, 1071 lines each) and sampled doilies (degree 3)."""
import numpy as np, itertools, random, math, sys
from fractions import Fraction as Fr
from geometry import geometry
from engine import omega
random.seed(int(sys.argv[1])); DQM = int(sys.argv[2])
pts, lines, signs = geometry("W", 4)
key = {p.tobytes(): i for i, p in enumerate(pts)}; lineidx = {l: i for i, l in enumerate(lines)}
L = np.array(lines); P = np.stack(pts).astype(np.int64)
def om_all(c):
    c = c.astype(np.int64); return (P[:, :4] @ c[4:] + P[:, 4:] @ c[:4]) % 2
def tv(c):
    img = (P + np.outer(om_all(c), c.astype(np.int64))) % 2
    return np.array([key[r.astype(np.uint8).tobytes()] for r in img])
def orbits(gens):
    parent = np.arange(len(lines))
    def f(i):
        while parent[i] != i: parent[i] = parent[parent[i]]; i = parent[i]
        return i
    for g in gens:
        img = np.sort(g[L], axis=1)
        for i in range(len(lines)):
            a, b = f(i), f(lineidx[tuple(img[i])])
            if a != b: parent[a] = b
    gr = {}
    for i in range(len(lines)): gr.setdefault(f(i), []).append(i)
    return [frozenset(x) for x in gr.values()]
wit = []
for c in itertools.product([0, 1], repeat=8):
    c = np.array(c); qf = lambda p: (int(p[:4] @ p[4:]) + int(c @ p)) % 2
    sing = [qf(p) == 0 for p in pts]
    if sum(sing) == 119:
        wit.append((Fr(DQM, 1071), frozenset(i for i, l in enumerate(lines) if all(sing[v] for v in l))))
vecs = [np.array(v) for v in itertools.product([0, 1], repeat=8) if any(v)]
def rnd_doily():
    while True:
        u = random.sample(vecs, 4)
        if omega(u[0], u[1]) == 1 and omega(u[2], u[3]) == 1 and all(omega(u[i], u[j]) == 0 for i in (0, 1) for j in (2, 3)):
            S = set()
            for co in itertools.product([0, 1], repeat=4):
                w = sum(ci * bi for ci, bi in zip(co, u)) % 2
                if w.any(): S.add(w.astype(np.uint8).tobytes())
            return frozenset(i for i, l in enumerate(lines) if all(pts[v].tobytes() in S for v in l))
for _ in range(1500): wit.append((Fr(1, 5), rnd_doily()))
best = Fr(DQM * 5, 5355)
print("baseline deg W(7,2) >=", math.ceil(5355 * best), flush=True)
for trial in range(int(sys.argv[3])):
    d = random.choice([1, 2, 2, 3, 3, 4])
    X = random.sample(vecs, d)
    gens = [tv(c) for c in vecs if all(omega(c, x) == 0 for x in X)]
    for O in orbits(gens):
        r = max((rw for rw, S in wit if len(S) <= len(O) and S <= O), default=None)
        if r is None: continue
        ro = Fr(math.ceil(len(O) * r), len(O))
        if ro > best:
            best = ro; print(f"orbit |O|={len(O)} ratio {float(ro):.6f} -> deg W(7,2) >= {math.ceil(5355 * ro)}", flush=True)
print("BEST deg W(7,2) >=", math.ceil(5355 * best))

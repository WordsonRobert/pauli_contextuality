"""Profile bound (Theorem: profile) for Q-(7,2) under the stabiliser of an anisotropic plane E (and variants).
All constraints are valid for every assignment; the IP minimum is a rigorous lower bound on deg Q-(7,2)."""
import numpy as np, itertools, sys, random
from math import lcm
from geometry import geometry
from engine import omega
from ortools.sat.python import cp_model
random.seed(1)
pts, lines, signs = geometry("Q-", 4)
key = {p.tobytes(): i for i, p in enumerate(pts)}
q = lambda p: (int(p[:4] @ p[4:]) + int(p[0]) + int(p[4])) % 2
V8 = [np.array(v, dtype=np.uint8) for v in itertools.product([0, 1], repeat=8) if any(v)]
nons = [v for v in V8 if q(v) == 1]
sing = [v for v in V8 if q(v) == 0]
lineidx = {l: i for i, l in enumerate(lines)}
P = np.stack(pts).astype(np.int64)
def refl(c):
    # orthogonal transvection x -> x + omega(x,c) c, as a permutation of points
    perm = []
    for p in pts:
        y = (p + omega(p, c) * c) % 2
        perm.append(key[y.astype(np.uint8).tobytes()])
    return perm
def line_orbits(gens):
    parent = list(range(len(lines)))
    def f(i):
        while parent[i] != i: parent[i] = parent[parent[i]]; i = parent[i]
        return i
    for g in gens:
        for i, l in enumerate(lines):
            j = lineidx[tuple(sorted(g[v] for v in l))]
            a, b = f(i), f(j)
            if a != b: parent[a] = b
    roots = {}
    lab = [roots.setdefault(f(i), len(roots)) for i in range(len(lines))]
    return lab, len(roots)
def lines_in(mask):   # mask: boolean per point
    return [i for i, l in enumerate(lines) if mask[l[0]] and mask[l[1]] and mask[l[2]]]
def perp_mask(vecs):
    return [all(omega(p, v) == 0 for v in vecs) for p in pts]

# anisotropic plane E (any; all conjugate)
a = nons[0]
b = next(v for v in nons if omega(a, v) == 1 and q((a + v) % 2) == 1)
E = [a, b, (a + b) % 2]
groups = {}
groups["Stab(E)"] = [c for c in nons if all(omega(c, e) == 0 for e in E)] + E
# variant: stabiliser of a non-singular point a (reflections in a and in nonsingular c perp a)
groups["Stab(a)"] = [c for c in nons if omega(c, a) == 0]
# variant: stabiliser of a singular point p
p0 = sing[0]
groups["Stab(p)"] = [c for c in nons if omega(c, p0) == 0]

# witnesses (degree known exactly): parabolic 7-sections (63), tangent 7-sections (36),
# Q+(5,2) sections E'^perp (21), Q-(5,2) sections H^perp (9), doilies (3, sampled)
wit = []
for c in nons: wit.append((63, lines_in(perp_mask([c]))))
for s in sing: wit.append((36, lines_in(perp_mask([s]))))
planes = set()
for x, y in itertools.combinations(nons, 2):
    z = (x + y) % 2
    if omega(x, y) == 1 and q(z) == 1:
        k = frozenset(v.tobytes() for v in (x, y, z))
        if k not in planes:
            planes.add(k); wit.append((21, lines_in(perp_mask([x, y]))))
hyp = set()
for x in sing:
    for y in sing:
        if omega(x, y) == 1:
            k = frozenset(v.tobytes() for v in (x, y, (x + y) % 2))
            if k not in hyp:
                hyp.add(k); wit.append((9, lines_in(perp_mask([x, y]))))
# doilies: a nonsingular, then a 4-dim nondegenerate subspace of a^perp/a  <-> 5-dim X = <a> + U4, U4 nondeg in a^perp
ap = [v for v in V8 if omega(v, a) == 0 and not np.array_equal(v, a)]
cnt = 0
while cnt < 4000:
    c = random.choice(nons)
    perpc = [v for v in V8 if omega(v, c) == 0 and not np.array_equal(v, c)]
    u1 = random.choice(perpc); u2 = random.choice([v for v in perpc if omega(v, u1) == 1])
    rest = [v for v in perpc if omega(v, u1) == 0 and omega(v, u2) == 0]
    u3 = random.choice(rest); cand = [v for v in rest if omega(v, u3) == 1]
    if not cand: continue
    u4 = random.choice(cand)
    span = set()
    basis = [c, u1, u2, u3, u4]
    for co in itertools.product([0, 1], repeat=5):
        w = sum(ci * bi for ci, bi in zip(co, basis)) % 2
        if w.any(): span.add(w.astype(np.uint8).tobytes())
    mask = [p.tobytes() in span for p in pts]
    L = lines_in(mask)
    if len(L) == 15 and sum(mask) == 15:
        wit.append((3, L)); cnt += 1
print("witnesses:", len(wit))

for name, gens in groups.items():
    lab, r = line_orbits([refl(c) for c in gens])
    sizes = [lab.count(i) for i in range(r)]
    cons = set()
    for d, L in wit:
        vec = [0] * r
        for i in L: vec[lab[i]] += 1
        cons.add((d, tuple(vec)))
    M = lcm(*sizes)
    m = cp_model.CpModel()
    n = [m.NewIntVar(0, sizes[i], f"n{i}") for i in range(r)]
    for d, vec in cons:
        m.Add(sum(vec[i] * (M // sizes[i]) * n[i] for i in range(r)) >= d * M)
    m.Minimize(sum(n))
    sv = cp_model.CpSolver(); sv.parameters.max_time_in_seconds = 120; sv.parameters.num_workers = 1
    st = sv.Solve(m)
    # LP relaxation
    from scipy.optimize import linprog
    A = [[-vec[i] / sizes[i] for i in range(r)] for d, vec in cons]; bvec = [-d for d, vec in cons]
    lp = linprog(np.ones(r), A_ub=A, b_ub=bvec, bounds=[(0, s) for s in sizes], method="highs")
    print(f"{name}: {r} line orbits sizes {sizes}; {len(cons)} distinct constraints; LP = {lp.fun:.3f}; "
          f"IP = {sv.ObjectiveValue():.0f} ({sv.StatusName(st)}); profile {[int(sv.Value(x)) for x in n]}", flush=True)

"""Target C: look for SMALL line-orbits O (of any subgroup H of O^-(8,2)) that contain a whole doily.
Then deg O >= ceil(|O|/5), and deg Q-(7,2) >= ceil(1071*ceil(|O|/5)/|O|)."""
import numpy as np, itertools, random, math, sys, collections
from geometry import geometry
from engine import omega
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
pts, lines, signs = geometry("Q-", 4)
key = {p.tobytes(): i for i, p in enumerate(pts)}; lineidx = {l: i for i, l in enumerate(lines)}
L = np.array(lines); P = np.stack(pts).astype(np.int64)
q = lambda p: (int(p[:4] @ p[4:]) + int(p[0]) + int(p[4])) % 2
V8 = [np.array(v, dtype=np.uint8) for v in itertools.product([0, 1], repeat=8) if any(v)]
nons = [v for v in V8 if q(v) == 1]
def om_all(c):
    c = c.astype(np.int64); return (P[:, :4] @ c[4:] + P[:, 4:] @ c[:4]) % 2
def refl(c):
    img = (P + np.outer(om_all(c), c.astype(np.int64))) % 2
    return np.array([key[r.astype(np.uint8).tobytes()] for r in img])
R = [refl(c) for c in nons]
# all doilies
doil = set()
cpt = 0
while cpt < 40000 and len(doil) < 45696:
    cpt += 1
    c = random.choice(nons)
    perpc = [v for v in V8 if omega(v, c) == 0 and not np.array_equal(v, c)]
    u1 = random.choice(perpc); u2 = random.choice([v for v in perpc if omega(v, u1) == 1])
    rest = [v for v in perpc if omega(v, u1) == 0 and omega(v, u2) == 0]
    u3 = random.choice(rest); cand = [v for v in rest if omega(v, u3) == 1]
    if not cand: continue
    u4 = random.choice(cand)
    S = set()
    for co in itertools.product([0, 1], repeat=5):
        w = sum(ci * bi for ci, bi in zip(co, [c, u1, u2, u3, u4])) % 2
        if w.any(): S.add(w.astype(np.uint8).tobytes())
    mask = np.array([p.tobytes() in S for p in pts])
    Lm = np.nonzero(mask[L].all(axis=1))[0]
    if len(Lm) == 15: doil.add(tuple(sorted(Lm.tolist())))
    if cpt % 20000 == 0: print("sampled", cpt, "distinct doilies", len(doil), flush=True)
D = np.array(sorted(doil))
print("doilies:", len(D), flush=True)
def compose(a, b): return a[b]           # apply b then a
def perm_order(g):
    seen = np.zeros(len(g), bool); o = 1
    for i in range(len(g)):
        if not seen[i]:
            j = i; c = 0
            while not seen[j]: seen[j] = True; j = g[j]; c += 1
            o = o * c // math.gcd(o, c)
    return o
def line_perm(g): return np.array([lineidx[tuple(sorted(g[v] for v in l))] for l in lines])
def orbits_of(gens_lines):
    parent = np.arange(len(lines))
    def f(i):
        while parent[i] != i: parent[i] = parent[parent[i]]; i = parent[i]
        return i
    for g in gens_lines:
        for i in range(len(lines)):
            a, b = f(i), f(g[i])
            if a != b: parent[a] = b
    return np.array([f(i) for i in range(len(lines))])
best = (216, None)
results = collections.Counter()
for trial in range(int(sys.argv[2]) if len(sys.argv) > 2 else 300):
    # random element: product of random reflections; then random power -> various orders
    g = np.arange(len(pts))
    for _ in range(random.randint(2, 12)): g = compose(R[random.randrange(len(R))], g)
    o = perm_order(g)
    if o == 1: continue
    p = random.choice([d for d in range(2, o + 1) if o % d == 0])
    h = np.arange(len(pts))
    for _ in range(o // p): h = compose(g, h)         # element of order p
    gens = [line_perm(h)]
    if random.random() < 0.4:                          # sometimes a 2-generator group
        g2 = np.arange(len(pts))
        for _ in range(random.randint(1, 4)): g2 = compose(R[random.randrange(len(R))], g2)
        gens.append(line_perm(g2))
    lab = orbits_of(gens)
    size = collections.Counter(lab.tolist())
    inside = lab[D]                                    # labels of the 15 lines of each doily
    full = np.all(inside == inside[:, :1], axis=1)
    for idx in np.nonzero(full)[0]:
        O = int(inside[idx, 0]); s = size[O]
        lb = math.ceil(s / 5); bound = math.ceil(1071 * lb / s)
        results[(s, len(gens))] += 1
        if bound > best[0]:
            best = (bound, (s, p, len(gens)))
            print(f"NEW: orbit size {s} (element order {p}, {len(gens)} gens) contains a doily -> deg O >= {lb} -> deg Q-(7,2) >= {bound}", flush=True)
print("orbit sizes containing doilies (size, #gens): counts", sorted(results.items())[:40])
print("BEST", best)

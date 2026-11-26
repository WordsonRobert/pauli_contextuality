"""Cascade in Q+(9,2): orbits O of reflection subgroups of O+(10,2) that contain an elliptic section E'^perp
(a copy of Q-(7,2), degree >= 216, 1071 lines). deg O >= ceil(|O|*216/1071); then deg Q+(9,2) >= ceil(23715*deg O/|O|)."""
import numpy as np, itertools, random, math, sys
from geometry import geometry
from engine import omega
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
DQM = int(sys.argv[2]) if len(sys.argv) > 2 else 216
pts, lines, signs = geometry("Q+", 5)
key = {p.tobytes(): i for i, p in enumerate(pts)}
lineidx = {l: i for i, l in enumerate(lines)}
L = np.array(lines)
q = lambda p: int(p[:5] @ p[5:]) % 2
V = [np.array(v, dtype=np.uint8) for v in itertools.product([0, 1], repeat=10) if any(v)]
nons = [v for v in V if q(v) == 1]
P = np.stack(pts).astype(np.int64)
def om_all(c):
    c = c.astype(np.int64)
    return (P[:, :5] @ c[5:] + P[:, 5:] @ c[:5]) % 2
def refl(c):
    w = om_all(c)
    img = (P + np.outer(w, c.astype(np.int64))) % 2
    return np.array([key[r.astype(np.uint8).tobytes()] for r in img])
def orbits(gens):
    parent = np.arange(len(lines))
    def f(i):
        while parent[i] != i: parent[i] = parent[parent[i]]; i = parent[i]
        return i
    for g in gens:
        img = np.sort(g[L], axis=1)
        for i in range(len(lines)):
            j = lineidx[tuple(img[i])]
            a, b = f(i), f(j)
            if a != b: parent[a] = b
    groups = {}
    for i in range(len(lines)): groups.setdefault(f(i), []).append(i)
    return [frozenset(x) for x in groups.values()]
def section(e1, e2):
    m = (om_all(e1) == 0) & (om_all(e2) == 0)
    return frozenset(i for i, l in enumerate(lines) if m[l[0]] and m[l[1]] and m[l[2]])
secs = []
while len(secs) < 300:
    a = random.choice(nons); b = random.choice(nons)
    if omega(a, b) == 1 and q((a + b) % 2) == 1:
        S = section(a, b)
        assert len(S) == 1071
        secs.append(S)
print("sampled elliptic sections:", len(secs), flush=True)
best = math.ceil(23715 * DQM / 1071)
print("baseline deg Q+(9,2) >=", best, flush=True)
for trial in range(int(sys.argv[3]) if len(sys.argv) > 3 else 12):
    d = random.choice([1, 2, 2, 3])
    X = random.sample(V, d)
    perp = [c for c in nons if all(omega(c, x) == 0 for x in X)]
    gens = [refl(c) for c in perp]
    orbs = orbits(gens)
    sizes = sorted(len(O) for O in orbs)
    for O in orbs:
        if len(O) <= 1071: continue
        if any(S <= O for S in secs):
            lb = math.ceil(len(O) * DQM / 1071)
            up = math.ceil(23715 * lb / len(O))
            flag = "  <-- improves" if up > best else ""
            print(f"dimX={d} orbit |O|={len(O)} contains an elliptic section: deg O >= {lb} -> deg Q+(9,2) >= {up}{flag}", flush=True)
            best = max(best, up)
    print(f"  trial {trial} dimX={d}: orbit sizes {sizes}", flush=True)
print("BEST", best)

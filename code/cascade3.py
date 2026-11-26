"""Cascade step 3: orbits O (757..1070 lines) of random small subgroups that contain some O_a' (ratio >= 152/756).
Then deg O >= ceil(|O|*152/756) and deg Q-(7,2) >= ceil(1071*that/|O|)."""
import numpy as np, itertools, random, math, sys
from fractions import Fraction as Fr
from geometry import geometry
from engine import omega
random.seed(int(sys.argv[1])); NT = int(sys.argv[2])
pts, lines, signs = geometry("Q-", 4)
key = {p.tobytes(): i for i, p in enumerate(pts)}; lineidx = {l: i for i, l in enumerate(lines)}
L = np.array(lines); P = np.stack(pts).astype(np.int64)
q = lambda p: (int(p[:4] @ p[4:]) + int(p[0]) + int(p[4])) % 2
V8 = [np.array(v, dtype=np.int64) for v in itertools.product([0, 1], repeat=8) if any(v)]
nons = [v for v in V8 if q(v) == 1]
def om_all(c): return (P[:, :4] @ c[4:] + P[:, 4:] @ c[:4]) % 2
def refl(c):
    img = (P + np.outer(om_all(c), c)) % 2
    return np.array([key[r.astype(np.uint8).tobytes()] for r in img])
R = [refl(c) for c in nons]
Oas = []
for a in nons:
    m = om_all(a) == 0
    Oas.append(np.nonzero(~m[L].all(axis=1))[0])
def line_perm(g): return np.array([lineidx[tuple(sorted(g[v] for v in l))] for l in lines])
def orbit_labels(gl):
    parent = np.arange(len(lines))
    def f(i):
        while parent[i] != i: parent[i] = parent[parent[i]]; i = parent[i]
        return i
    for g in gl:
        for i in range(len(lines)):
            a, b = f(i), f(g[i])
            if a != b: parent[a] = b
    return np.array([f(i) for i in range(len(lines))])
r0 = Fr(152, 756); best = 216
import collections; seen = collections.Counter()
for t in range(NT):
    gens = []
    for _ in range(random.choice([1, 2, 2, 3])):
        g = np.arange(len(pts))
        for _ in range(random.randint(1, 10)): g = R[random.randrange(len(R))][g]
        gens.append(line_perm(g))
    lab = orbit_labels(gens)
    sizes = collections.Counter(lab.tolist())
    for O in Oas:
        ls = set(lab[O].tolist())
        if len(ls) == 1:
            s = sizes[ls.pop()]
            if s == 756 or s == 1071: continue
            seen[s] += 1
            lb = math.ceil(s * r0); bnd = math.ceil(1071 * Fr(lb, s))
            if bnd > best:
                best = bnd; print(f"NEW orbit size {s} contains O_a: deg O >= {lb} -> deg Q-(7,2) >= {bnd}", flush=True)
print("orbit sizes (other than 756, 1071) containing some O_a:", dict(seen)); print("BEST", best)

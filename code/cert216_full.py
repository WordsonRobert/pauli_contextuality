"""Full elementary certificate for deg Q-(7,2) >= 216 over ALL 136 non-singular a (no group theory used):
 (1) every one of the 45696 doilies of Q-(7,2) is covered 4 times by 10 odd grids  => each doily has degree >= 3
 (2) for every non-singular a, the doilies inside O_a cover each of its 756 lines exactly 80 times (4032 doilies)
     => deg O_a >= ceil(4032*3/80) = 152
 (3) the 136 sets O_a cover each line of Q-(7,2) exactly 96 times  => deg Q-(7,2) >= ceil(136*152/96) = 216."""
import numpy as np, itertools, collections, math, time
from geometry import geometry
from engine import omega
t0 = time.time()
pts, lines, signs = geometry("Q-", 4)
q = lambda p: (int(p[:4] @ p[4:]) + int(p[0]) + int(p[4])) % 2
P = np.stack(pts).astype(np.int64); L = np.array(lines)
V8 = [np.array(v, dtype=np.int64) for v in itertools.product([0, 1], repeat=8) if any(v)]
nons = [v for v in V8 if q(v) == 1]
def om_all(c): return (P[:, :4] @ c[4:] + P[:, 4:] @ c[:4]) % 2
OM = {v.tobytes(): om_all(v) == 0 for v in V8}
doilies = set()
for c in nons:
    Wc = [v for v in V8 if omega(v, c) == 0 and not np.array_equal(v, c)]
    for u, v in itertools.combinations(Wc, 2):
        if omega(u, v) == 1:
            m = OM[c.tobytes()] & OM[u.tobytes()] & OM[v.tobytes()]
            D = np.nonzero(m[L].all(axis=1))[0]
            if len(D) == 15: doilies.add(tuple(D.tolist()))
doilies = sorted(doilies); print("doilies", len(doilies), f"{time.time()-t0:.0f}s", flush=True)
ptsets = [frozenset(l) for l in lines]
bad = 0
for D in doilies:
    grids = set()
    for r in itertools.combinations(D, 3):
        if len(ptsets[r[0]] | ptsets[r[1]] | ptsets[r[2]]) != 9: continue
        s9 = ptsets[r[0]] | ptsets[r[1]] | ptsets[r[2]]
        cols = [k for k in D if k not in r and ptsets[k] <= s9 and all(len(ptsets[k] & ptsets[j]) == 1 for j in r)]
        if len(cols) == 3: grids.add(tuple(sorted(r + tuple(cols))))
    c4 = collections.Counter(i for g in grids for i in g)
    oddall = all(sum(signs[i] for i in g) % 2 == 1 for g in grids)
    if not (len(grids) == 10 and oddall and set(c4.values()) == {4} and len(c4) == 15): bad += 1
print("(1) doilies failing the 10-odd-grid certificate:", bad, f"{time.time()-t0:.0f}s", flush=True)
covQ = collections.Counter(); ok2 = True
for a in nons:
    Oa = set(np.nonzero(~OM[a.tobytes()][L].all(axis=1))[0].tolist())
    fam = [D for D in doilies if Oa.issuperset(D)]
    cov = collections.Counter(i for D in fam for i in D)
    ok2 &= len(Oa) == 756 and len(fam) == 4032 and set(cov.values()) == {80} and len(cov) == 756
    for i in Oa: covQ[i] += 1
print("(2) every O_a: 756 lines, 4032 doilies, uniform coverage 80:", ok2, flush=True)
print("(3) coverage of Q- lines by the 136 O_a:", set(covQ.values()), " -> bound", math.ceil(136 * 152 / 96), f"{time.time()-t0:.0f}s")

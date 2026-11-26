"""Generate a Lean-friendly certificate for deg Q-(7,2) >= 216 using ONLY:
  (L1) odd-cycle lemma: an odd cycle forces >= 1 violated line;
  (L2) uniform-cover lemma: if a family F of sub-configurations, each of degree >= d, covers every line of C
       exactly c times, then deg C >= ceil(|F| d / c).
Chain: grids (odd cycles) -> doilies (>=3) -> O_a (>=152) -> Q-(7,2) (>=216)."""
import numpy as np, itertools, json, math, collections
from geometry import geometry
from engine import omega
pts, lines, signs = geometry("Q-", 4)
q = lambda p: (int(p[:4] @ p[4:]) + int(p[0]) + int(p[4])) % 2
P = np.stack(pts).astype(np.int64); L = np.array(lines)
V8 = [np.array(v, dtype=np.int64) for v in itertools.product([0, 1], repeat=8) if any(v)]
nons = [v for v in V8 if q(v) == 1]
def om_all(c): return (P[:, :4] @ c[4:] + P[:, 4:] @ c[:4]) % 2
def lines_in(mask): return [int(i) for i in np.nonzero(mask[L].all(axis=1))[0]]
# --- all doilies: (c nonsingular, nondegenerate plane <u,v> in c^perp) -> lines inside {w: w.c=w.u=w.v=0}
doilies = set()
for c in nons:
    Wc = [v for v in V8 if omega(v, c) == 0 and not np.array_equal(v, c)]
    for u in Wc:
        for v in Wc:
            if omega(u, v) == 1:
                m = (om_all(c) == 0) & (om_all(u) == 0) & (om_all(v) == 0)
                D = lines_in(m)
                if len(D) == 15: doilies.add(tuple(D))
doilies = sorted(doilies)
print("doilies in Q-(7,2):", len(doilies))
cov = collections.Counter(i for D in doilies for i in D)
print("Q-(7,2) lines covered by doilies uniformly:", set(cov.values()))
def grids_of(D):
    Ds = [lines[i] for i in D]; out = []
    for r in itertools.combinations(range(15), 3):
        pts9 = [v for k in r for v in Ds[k]]
        if len(set(pts9)) != 9: continue
        s9 = set(pts9)
        cols = [k for k in range(15) if k not in r and set(Ds[k]) <= s9 and all(len(set(Ds[k]) & set(Ds[j])) == 1 for j in r)]
        if len(cols) == 3:
            g = tuple(sorted(D[k] for k in list(r) + cols))
            out.append(g)
    return sorted(set(out))
def odd(g):
    cnt = collections.Counter(v for i in g for v in lines[i])
    return all(x == 2 for x in cnt.values()) and sum(signs[i] for i in g) % 2 == 1
# --- the witness O_a
a = next(v for v in V8 if q(v) == 1)
inside_a = lines_in(om_all(a) == 0)
Oa = sorted(set(range(len(lines))) - set(inside_a))
Oset = set(Oa)
fam = [D for D in doilies if set(D) <= Oset]
covO = collections.Counter(i for D in fam for i in D)
print("O_a:", len(Oa), "lines; doilies inside:", len(fam), "; coverage values", set(covO.values()), "; all O_a lines covered:", len(covO) == len(Oa))
# grid certificates for those doilies
gcert = {}
okg = True
for D in fam:
    gs = grids_of(D)
    c4 = collections.Counter(i for g in gs for i in g)
    okg &= len(gs) == 10 and all(odd(g) for g in gs) and set(c4.values()) == {4}
    gcert[",".join(map(str, D))] = gs
print("every doily in the family: 10 odd grids covering each line 4 times:", okg)
cO = list(set(covO.values()))[0]
lbO = math.ceil(len(fam) * 3 / cO)
print(f"=> deg O_a >= ceil({len(fam)}*3/{cO}) = {lbO}")
# family of O_{a'} for all 136 non-singular a': coverage of each Q- line
covQ = collections.Counter()
for ap in nons:
    ins = set(lines_in(om_all(ap) == 0))
    for i in range(len(lines)):
        if i not in ins: covQ[i] += 1
cQ = set(covQ.values())
print("each Q- line lies in", cQ, "of the 136 sets O_a'")
c = list(cQ)[0]
print(f"=> deg Q-(7,2) >= ceil(136*{lbO}/{c}) = {math.ceil(136 * lbO / c)}")
json.dump({"points": [p.tolist() for p in P], "lines": lines, "signs": signs,
           "quadratic_form": "q(x|z) = x.z + x1 + z1 (mod 2)", "a": a.tolist(), "O_a": Oa,
           "doilies_in_O_a": [list(D) for D in fam], "grids": gcert,
           "coverage_doilies_in_O_a": cO, "coverage_O_aprime_in_Qm": c},
          open("../data/cert216_Qm7.json", "w"))

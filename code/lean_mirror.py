"""Reference implementation of lean/PauliContextuality/Qminus.lean using the SAME bit-packed encoding
(bits 0..3 = x, bits 4..7 = z). Run it to get the intermediate counts the Lean checker must reproduce."""
import itertools, collections
pc = lambda v: bin(v).count("1")
xp = lambda p: p % 16
zp = lambda p: p // 16
om = lambda p, q: (pc(xp(p) & zp(q)) + pc(zp(p) & xp(q))) % 2 == 1
qm = lambda p: (pc(xp(p) & zp(p)) + xp(p) % 2 + zp(p) % 2) % 2 == 1
ycnt = lambda p: pc(xp(p) & zp(p))
def sgn(a, b, c):
    k = ycnt(a) + ycnt(b) + ycnt(c) + 2 * (pc(zp(a) & xp(b)) + pc((zp(a) ^ zp(b)) & xp(c)))
    return k % 4 == 2
pts = [p for p in range(256) if p != 0 and not qm(p)]
ptset = set(pts)
lines = []
for a in pts:
    for b in pts:
        if a < b and not om(a, b):
            c = a ^ b
            if b < c and c in ptset: lines.append((a, b, c))
signs = [sgn(*l) for l in lines]
nonsing = [p for p in range(256) if p != 0 and qm(p)]
print("points", len(pts), "lines", len(lines), "negative", sum(signs), "nonsingular", len(nonsing))
def lines_in_perp(vs):
    return tuple(i for i, (a, b, c) in enumerate(lines) if all(not om(a, v) and not om(b, v) and not om(c, v) for v in vs))
# speed: precompute per-vector perp line sets
perp = {v: frozenset(lines_in_perp([v])) for v in range(1, 256)}
doil = set()
for c in nonsing:
    Wc = [v for v in range(1, 256) if v != c and not om(v, c)]
    for u, v in itertools.combinations(Wc, 2):
        if om(u, v):
            D = perp[c] & perp[u] & perp[v]
            if len(D) == 15: doil.add(tuple(sorted(D)))
doil = sorted(doil)
cov = collections.Counter(i for D in doil for i in D)
print("doilies", len(doil), "coverage", set(cov.values()))
pset = [frozenset(l) for l in lines]
def doilyOK(D):
    gr = set()
    for r in itertools.combinations(D, 3):
        s9 = pset[r[0]] | pset[r[1]] | pset[r[2]]
        if len(s9) != 9: continue
        cols = [k for k in D if k not in r and pset[k] <= s9 and all(len(pset[k] & pset[j]) == 1 for j in r)]
        if len(cols) == 3: gr.add(tuple(sorted(r + tuple(cols))))
    c4 = collections.Counter(i for g in gr for i in g)
    return len(gr) == 10 and all(sum(signs[i] for i in g) % 2 == 1 for g in gr) and set(c4.values()) == {4} and len(c4) == 15
print("all doilies OK:", all(doilyOK(D) for D in doil))
allL = set(range(len(lines)))
covQ = collections.Counter(); ok = True
for a in nonsing:
    O = allL - perp[a]
    fam = [D for D in doil if O.issuperset(D)]
    cv = collections.Counter(i for D in fam for i in D)
    ok &= len(O) == 756 and len(fam) == 4032 and set(cv.values()) == {80} and len(cv) == 756
    for i in O: covQ[i] += 1
print("every O_a: 756 lines, 4032 doilies, coverage 80:", ok, "| coverage of Q- by the O_a:", set(covQ.values()))
print("arithmetic: 10*1 > 4*2:", 10 > 8, "| 4032*3 > 80*151:", 4032 * 3 > 80 * 151, "| 136*152 > 96*215:", 136 * 152 > 96 * 215)
print("=> deg Q-(7,2) >= 216" if ok and set(covQ.values()) == {96} else "CERTIFICATE FAILED")

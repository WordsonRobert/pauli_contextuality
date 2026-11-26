#!/usr/bin/env python3
"""Standalone certificate checker for every finite fact used in the paper.

Deliberately independent of the construction code: it re-implements Pauli products, line enumeration
and violation counting from scratch (numpy only).  Each check prints PASS/FAIL.

Conventions: a Pauli on n qubits is a 0/1 vector (x|z) of length 2n; its canonical Hermitian operator is
P(x|z) = i^{x.z} X^x Z^z.  A line is a set {a, b, a+b} of distinct non-zero pairwise-commuting points; its sign
e in {0,1} is defined by P(a)P(b)P(a+b) = (-1)^e I.
"""
import itertools, sys, os
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = []


def check(name, ok, detail=""):
    RESULTS.append(ok)
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))


# ----------------------------------------------------------------------------- Pauli algebra
def P(s):
    n = len(s); v = np.zeros(2 * n, dtype=np.int64)
    for i, c in enumerate(s):
        v[i] = c in "XY"; v[n + i] = c in "ZY"
    return v


def om(a, b):
    n = len(a) // 2
    return int(a[:n] @ b[n:] + a[n:] @ b[:n]) % 2


def sign(ops):
    """e with prod P(op) = (-1)^e I; None if the product is not +-I."""
    n = len(ops[0]) // 2
    k, x, z = 0, np.zeros(n, np.int64), np.zeros(n, np.int64)
    for p in ops:
        x2, z2 = p[:n], p[n:]
        k += int(x2 @ z2) + 2 * int(z @ x2)
        x, z = (x + x2) % 2, (z + z2) % 2
    if x.any() or z.any() or k % 2:
        return None
    return (k % 4) // 2


def all_vecs(d):
    return [np.array(t, dtype=np.int64) for t in itertools.product([0, 1], repeat=d) if any(t)]


def lines_of(points):
    key = {p.tobytes(): i for i, p in enumerate(points)}
    out = set()
    for i, j in itertools.combinations(range(len(points)), 2):
        if om(points[i], points[j]) == 0:
            k = key.get(((points[i] + points[j]) % 2).tobytes())
            if k is not None:
                out.add(tuple(sorted((i, j, k))))
    return sorted(out)


def signs_of(points, lines):
    return [sign([points[a], points[b], points[c]]) for a, b, c in lines]


def violations(x, lines, signs):
    return sum((x[a] ^ x[b] ^ x[c] ^ s) for (a, b, c), s in zip(lines, signs))


def exact_degree(npts, lines, signs):
    """Exhaustive (Gray code) -- only for small point sets."""
    inc = [[] for _ in range(npts)]
    for r, l in enumerate(lines):
        for v in l: inc[v].append(r)
    viol = list(signs); cur = sum(viol); best = cur
    for g in range(1, 1 << npts):
        v = (g & -g).bit_length() - 1
        for r in inc[v]:
            cur += -1 if viol[r] else 1; viol[r] ^= 1
        best = min(best, cur)
    return best


def quad(kind, n):
    if kind == "W":
        return lambda p: 0
    if kind == "Q+":
        return lambda p: int(p[:n] @ p[n:]) % 2
    if kind == "Q-":
        return lambda p: (int(p[:n] @ p[n:]) + int(p[0]) + int(p[n])) % 2


def geometry(kind, n):
    q = quad(kind, n)
    pts = [p for p in all_vecs(2 * n) if q(p) == 0]
    L = lines_of(pts)
    return pts, L, signs_of(pts, L)


# ============================================================================ 1. gadget template
def template_checks():
    A, B = P("ZIII"), P("IZII")
    r1 = [A, B, (A + B) % 2]
    r2 = [P(s) for s in ("IXIZ", "XIZI", "XXZZ")]
    r3 = [P(s) for s in ("ZXIZ", "XZZI", "YYZZ")]
    grid = [r1, r2, r3] + [[r1[j], r2[j], r3[j]] for j in range(3)]
    valid = all(all(om(a, b) == 0 for a, b in itertools.combinations(l, 2)) and
                not ((l[0] + l[1] + l[2]) % 2).any() for l in grid)
    check("T1 template: all 6 grid triples are commuting zero-sum triples", valid)
    pts = r1 + r2 + r3
    check("T2 template: 9 grid points distinct and non-zero",
          len({p.tobytes() for p in pts}) == 9 and all(p.any() for p in pts))
    lam = sum(sign(l) for l in grid) % 2
    check("T3 template: the 6-line grid cycle has odd sign (lambda = 1)", lam == 1, f"lambda={lam}")
    priv = lambda p: tuple(p[[2, 3, 6, 7]])
    check("T4 template: private parts of p2j, p3j non-zero, equal within a column, distinct across columns",
          all(any(priv(r2[j])) and priv(r2[j]) == priv(r3[j]) for j in range(3)) and
          len({priv(r2[j]) for j in range(3)}) == 3)
    mixed_ok = True
    for choice in itertools.product([0, 1], repeat=3):
        if choice in [(0, 0, 0), (1, 1, 1)]:
            continue
        s = sum((r3[j] if choice[j] else r2[j]) for j in range(3)) % 2
        mixed_ok &= bool(s.any())
    check("T5 template: the 6 mixed row-selections (one point per column) do not sum to zero", mixed_ok)
    ycount = [int(p[:4] @ p[4:]) for p in r2 + r3]
    check("T6 template: every path point has an even number of Y's", all(c % 2 == 0 for c in ycount), str(ycount))


# ============================================================================ 2. chain block table
def chain_checks():
    lam = [np.array(v) for v in ((1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1))]
    check("C1 copy labels: distinct, non-zero, sum to 0, no three sum to 0",
          len({tuple(l) for l in lam}) == 4 and not (sum(lam) % 2).any() and
          all(((a + b + c) % 2).any() for a, b, c in itertools.combinations(lam, 3)))
    # one generic equation on three blocks (9 qubits, Z-type, so only z-part matters)
    def copy(i, r):
        v = np.zeros(9, np.int64); v[3 * i:3 * i + 3] = lam[r]; return v
    seq = [copy(i, r) for r in range(4) for i in range(3)]
    aux = [sum(seq[:k + 2]) % 2 for k in range(9)]          # u_1..u_9
    pts = [copy(i, r) for i in range(3) for r in range(4)] + aux
    key = {p.tobytes(): i for i, p in enumerate(pts)}
    check("C2 one equation: 12 copies + 9 aux points pairwise distinct and non-zero",
          len(key) == 21 and all(p.any() for p in pts))
    chain = [(seq[0], seq[1], aux[0])] + [(aux[k - 1], seq[k + 1], aux[k]) for k in range(1, 9)] + \
            [(aux[8], seq[10], seq[11])]
    chain_idx = {tuple(sorted(key[p.tobytes()] for p in l)) for l in chain}
    check("C3 one equation: the 10 chain triples sum to zero", all(not (sum(l) % 2).any() for l in chain))
    zs = {t for t in itertools.combinations(range(21), 3) if not ((pts[t[0]] + pts[t[1]] + pts[t[2]]) % 2).any()}
    check("C4 one equation: zero-sum triples among its 21 points are exactly the 10 chain lines",
          zs == chain_idx, f"{len(zs)} found")
    supp = [tuple(i for i in range(3) if a[3 * i:3 * i + 3].any()) for a in aux]
    check("C5 aux supports: size >= 2; size 2 only for u_1 = {v0,v1} and u_9 = {v1,v2}",
          supp[0] == (0, 1) and supp[8] == (1, 2) and all(len(s) == 3 for s in supp[1:8]), str(supp))


# ============================================================================ 3. small exact degrees
def small_degree_checks():
    pts, L, S = geometry("W", 2)
    d = exact_degree(len(pts), L, S)
    check("D1 W(3,2): 15 points, 15 lines, 3 of sign 1, exact degree 3 (exhaustive)",
          len(pts) == 15 and len(L) == 15 and sum(S) == 3 and d == 3)
    ms = [["XI", "IX", "XX"], ["IZ", "ZI", "ZZ"], ["XZ", "ZX", "YY"]]
    g = [[P(s) for s in r] for r in ms]
    lines = [r for r in g] + [[g[i][j] for i in range(3)] for j in range(3)]
    lam = sum(sign(l) for l in lines) % 2
    check("D2 Mermin square: 6 lines of W(3,2), odd cycle sign => degree 1", lam == 1)
    pts3, L3, S3 = geometry("W", 3)
    wit = [int(t) for t in open(os.path.join(HERE, "witness_W5_2.txt"))]
    v = violations(wit, L3, S3)
    check("D3 W(5,2): 63 points, 315 lines, witness assignment violates 63 lines", len(L3) == 315 and v == 63, f"{v}")


# ============================================================================ 4. sections / embeddings
def find_doily(pts, L, S, n):
    """Find a non-degenerate 4-dim subspace (as span of 2 hyperbolic pairs) whose W(3,2)-lines are all in L.
    For a quadric, use instead a 5-dim parabolic section; we simply search for a 15-point/15-line
    sub-configuration that is the set of all lines inside span(T) for some subspace T."""
    key = {p.tobytes(): i for i, p in enumerate(pts)}
    Ls = set(L)
    rng = np.random.default_rng(1)
    for _ in range(20000):
        basis = [pts[i] for i in rng.choice(len(pts), 5, replace=False)]
        span = set()
        for c in itertools.product([0, 1], repeat=5):
            v = sum(ci * b for ci, b in zip(c, basis)) % 2
            if v.any(): span.add(v.tobytes())
        if len(span) != 31: continue
        sub = [key[b] for b in span if b in key]
        subset = set(sub)
        subL = [l for l in L if all(v in subset for v in l)]
        if len(sub) == 15 and len(subL) == 15:
            # generalized quadrangle check: every point on exactly 3 lines
            if all(sum(v in l for l in subL) == 3 for v in sub):
                return sub, subL
    return None, None


def section_checks():
    # Q-(7,2) on 4 qubits
    pts, L, S = geometry("Q-", 4)
    check("S1 Q-(7,2): 119 points, 1071 lines", len(pts) == 119 and len(L) == 1071)
    sub, subL = find_doily(pts, L, S, 4)
    if sub is None:
        check("S2 Q-(7,2): contains a doily (15 pts, 15 lines, 3 lines/point) of degree 3", False); return
    re = {v: i for i, v in enumerate(sub)}
    d = exact_degree(15, [tuple(re[v] for v in l) for l in subL], [S[L.index(l)] for l in subL])
    check("S2 Q-(7,2): contains a doily (15 pts, 15 lines, 3 lines/point) of degree 3", d == 3, f"degree {d}")
    # Q+(9,2) on 5 qubits and its elliptic section
    pts5, L5, S5 = geometry("Q+", 5)
    check("S3 Q+(9,2): 527 points, 23715 lines", len(pts5) == 527 and len(L5) == 23715)
    e1, e2 = P("IIIIY"), P("IIIYX")
    q = lambda p: int(p[:5] @ p[5:]) % 2
    aniso = q(e1) == q(e2) == q((e1 + e2) % 2) == 1 and om(e1, e2) == 1
    check("S4 E = <Y5, Y4X5>: non-degenerate and anisotropic (q = 1 on all 3 non-zero vectors)", aniso)
    inU = [om(p, e1) == 0 and om(p, e2) == 0 for p in pts5]
    secP = [i for i in range(len(pts5)) if inU[i]]
    secL = [l for l in L5 if all(inU[v] for v in l)]
    check("S5 section of Q+(9,2) by E^perp: 119 points, 1071 lines (an elliptic quadric Q-(7,2))",
          len(secP) == 119 and len(secL) == 1071)
    sp = [pts5[i] for i in secP]; reS = {v: i for i, v in enumerate(secP)}
    sL = [tuple(reS[v] for v in l) for l in secL]; sS = [S5[L5.index(l)] for l in secL]
    sub, subL = find_doily(sp, sL, sS, 5)
    ok = False
    if sub is not None:
        re = {v: i for i, v in enumerate(sub)}
        ok = exact_degree(15, [tuple(re[v] for v in l) for l in subL], [sS[sL.index(l)] for l in subL]) == 3
    check("S6 the section contains a doily of degree 3", ok)
    bound = -(-23715 * 215 // 1071)
    check("S7 arithmetic: ceil(1071/5) = 215 and ceil(23715*215/1071) = 4761 > 4743 = 23715/5",
          -(-1071 // 5) == 215 and bound == 4761 and 23715 // 5 == 4743)


# ============================================================================ 5. upper-bound witnesses
def witness_checks():
    for lab, kind, n, fn, target in [("U1", "W", 4, "witness_W7_2.txt", 1575),
                                     ("U2", "Q-", 4, "witness_Qm7_2.txt", 315),
                                     ("U3", "Q+", 5, "witness_Qp9_2.txt", 6975),
                                     ("U4", "Q-", 5, "witness_Qm9_2.txt", 7087),
                                     ("U5", "W", 5, "witness_W9_2.txt", 31479)]:
        path = os.path.join(HERE, fn)
        if not os.path.exists(path):
            check(f"{lab} {kind} n={n}: witness file missing", False); continue
        pts, L, S = geometry(kind, n)
        x = [int(t) for t in open(path)]
        v = violations(x, L, S)
        check(f"{lab} {kind}({2*n-1},2): {len(L)} lines, witness violates {v} (claimed {target})", v == target)


# ============================================================================ 6. rigidity (equality case)
def rigidity_checks():
    pts, L, S = geometry("W", 3)
    x = [int(t) for t in open(os.path.join(HERE, "witness_W5_2.txt"))]
    V = {l for l, s in zip(L, S) if x[l[0]] ^ x[l[1]] ^ x[l[2]] ^ s}
    counts = {}
    for c in all_vecs(6):
        qf = lambda p, c=c: (int(p[:3] @ p[3:]) + int(c @ p)) % 2
        Q = [l for l in L if all(qf(pts[v]) == 0 for v in l)]
        nsing = sum(qf(p) == 0 for p in pts)
        counts.setdefault((nsing, len(Q)), set()).add(len(V.intersection(Q)))
    desc = {k: sorted(v) for k, v in counts.items()}
    ok = desc.get((35, 105)) == [21] and desc.get((27, 45)) == [9]
    check("R1 rigidity: the optimal W(5,2) witness violates exactly 21 lines of every Q+(5,2) "
          "and exactly 9 of every Q-(5,2)", ok, str(desc))
    # doilies of W(5,2) = lines inside F^perp for each non-degenerate 2-space F
    seen, hits = set(), set()
    vecs = all_vecs(6)
    for a, b in itertools.combinations(vecs, 2):
        if om(a, b) != 1: continue
        F = frozenset(v.tobytes() for v in (a, b, (a + b) % 2))
        if F in seen: continue
        seen.add(F)
        inside = [all(om(pts[v], a) == 0 and om(pts[v], b) == 0 for v in l) for l in L]
        D = [l for l, i in zip(L, inside) if i]
        hits.add((len(D), len(V.intersection(D))))
    check("R2 rigidity: the witness violates exactly 3 lines in each of the %d doilies of W(5,2)" % len(seen),
          hits == {(15, 3)}, str(hits))


# ============================================================================ 7. cones / tangent sections
def cone_checks():
    # K1: Cone_1(Peres-Mermin square) on 3 qubits (vertex Z_3): exact degree 4 = 4 * 1 (exhaustive)
    ms = [["XI", "IX", "XX"], ["IZ", "ZI", "ZZ"], ["XZ", "ZX", "YY"]]
    base = [P(s) for r in ms for s in r]
    blines = [(3 * i, 3 * i + 1, 3 * i + 2) for i in range(3)] + [(j, j + 3, j + 6) for j in range(3)]
    def lift(v, t):            # v on 2 qubits -> v (x) Z^t on 3 qubits
        return np.array([v[0], v[1], 0, v[2], v[3], t], dtype=np.int64)
    cpts = [lift(v, t) for v in base for t in (0, 1)] + [P("IIZ")]
    key = {p.tobytes(): i for i, p in enumerate(cpts)}
    cl = set()
    for (i, j, k) in blines:
        for al, be in itertools.product([0, 1], repeat=2):
            tri = (lift(base[i], al), lift(base[j], be), lift(base[k], al ^ be))
            cl.add(tuple(sorted(key[t.tobytes()] for t in tri)))
    for v in base:
        cl.add(tuple(sorted((key[lift(v, 0).tobytes()], key[lift(v, 1).tobytes()], key[P("IIZ").tobytes()]))))
    cl = sorted(cl)
    induced = lines_of(cpts)
    d = exact_degree(len(cpts), cl, signs_of(cpts, cl))
    check("K1 Cone_1(Peres-Mermin): 19 points, 33 lines (= all lines on its points), exact degree 4 = 4*1",
          len(cpts) == 19 and len(cl) == 33 and sorted(induced) == cl and d == 4, f"degree {d}")
    # K2: lifted assignments attain 4*deg on the 4-qubit tangent sections Z4^perp (W, Q+, Q-)
    base = {"W": ("witness_W5_2.txt", 63)}
    for kind, target in [("W", 252), ("Q+", 84), ("Q-", 36)]:
        pts4, L4, S4 = geometry(kind, 4)
        p = P("IIIZ")
        keep = [i for i in range(len(pts4)) if om(pts4[i], p) == 0]
        ks = set(keep)
        sub = [(l, s) for l, s in zip(L4, S4) if all(v in ks for v in l)]
        # base assignment on 3 qubits: optimal W(5,2) witness restricted (optimal on Q+(5,2), Q-(5,2) by R1)
        pts3, L3, S3 = geometry("W", 3)
        y = [int(t) for t in open(os.path.join(HERE, "witness_W5_2.txt"))]
        key3 = {v.tobytes(): i for i, v in enumerate(pts3)}
        x = {}
        for i in keep:
            v = pts4[i]
            base_v = np.concatenate([v[0:3], v[4:7]])        # drop qubit 4
            x[i] = y[key3[base_v.tobytes()]] if base_v.any() else 0
        viol = sum((x[a] ^ x[b] ^ x[c] ^ s) for (a, b, c), s in sub)
        check(f"K2 tangent section Z4^perp of {kind}(7,2): {len(sub)} lines; lifted assignment violates {viol} = {target}",
              viol == target)


def structure_checks():
    # R3: structure of the optimal Q-(7,2) witness around an anisotropic plane E
    pts, L, S = geometry("Q-", 4)
    x = [int(t) for t in open(os.path.join(HERE, "witness_Qm7_2.txt"))]
    V = {l for l, s in zip(L, S) if x[l[0]] ^ x[l[1]] ^ x[l[2]] ^ s}
    q = quad("Q-", 4)
    tight = []
    for a in all_vecs(8):
        if q(a) == 1:
            k = sum(1 for l in V if all(om(a, pts[v]) == 0 for v in l))
            if k == 63: tight.append(a)
    ok = len(tight) == 3 and not (sum(tight) % 2).any()
    if ok:
        inE = [all(om(p, a) == 0 for a in tight) for p in pts]
        LE = [l for l in L if all(inE[v] for v in l)]
        ok = sum(inE) == 35 and len(LE) == 105 and len(V.intersection(LE)) == 21
    check("R3 optimal Q-(7,2) witness: exactly 3 tight parabolic sections a^perp, a in an anisotropic plane E; "
          "E^perp is a Q+(5,2) carrying exactly 21 violated lines", ok)


# ============================================================================ 8. the 756-line witness (deg Q-(7,2) >= 216)
def cascade_checks():
    import random
    rnd = random.Random(12345)
    pts, L, S = geometry("Q-", 4)
    q = quad("Q-", 4)
    key = {p.tobytes(): i for i, p in enumerate(pts)}
    lidx = {l: i for i, l in enumerate(L)}
    a = next(v for v in all_vecs(8) if q(v) == 1)
    out = [i for i, l in enumerate(L) if not all(om(a, pts[v]) == 0 for v in l)]
    check("A1 lines of Q-(7,2) not contained in a^perp (a non-singular): 756", len(out) == 756)
    # orbit check: reflections t_c (c non-singular, c perp a) generate a group transitive on these 756 lines
    gens = []
    for c in all_vecs(8):
        if q(c) == 1 and om(c, a) == 0:
            gens.append([key[((p + om(p, c) * c) % 2).tobytes()] for p in pts])
    parent = list(range(len(L)))
    def f(i):
        while parent[i] != i: parent[i] = parent[parent[i]]; i = parent[i]
        return i
    for g in gens:
        for i, l in enumerate(L):
            j = lidx[tuple(sorted(g[v] for v in l))]
            x, y = f(i), f(j)
            if x != y: parent[x] = y
    check("A2 the stabiliser of a (generated by reflections) is transitive on those 756 lines",
          len({f(i) for i in out}) == 1 and all(f(i) != f(out[0]) for i in range(len(L)) if i not in set(out)))
    # an explicit doily all of whose lines avoid a^perp
    outset = set(out); V8 = all_vecs(8)
    nons = [v for v in V8 if q(v) == 1]
    found = None
    for _ in range(200000):
        c = rnd.choice(nons)
        perpc = [v for v in V8 if om(v, c) == 0 and not np.array_equal(v, c)]
        u1 = rnd.choice(perpc); c2 = [v for v in perpc if om(v, u1) == 1]; u2 = rnd.choice(c2)
        rest = [v for v in perpc if om(v, u1) == 0 and om(v, u2) == 0]
        u3 = rnd.choice(rest); c4 = [v for v in rest if om(v, u3) == 1]
        if not c4: continue
        u4 = rnd.choice(c4)
        span = set()
        for co in itertools.product([0, 1], repeat=5):
            w = sum(ci * bi for ci, bi in zip(co, [c, u1, u2, u3, u4])) % 2
            if w.any(): span.add(w.tobytes())
        D = [i for i, l in enumerate(L) if all(pts[v].tobytes() in span for v in l)]
        if len(D) == 15 and set(D) <= outset:
            found = D; break
    ok = False
    if found:
        dp = sorted({v for i in found for v in L[i]}); re = {v: k for k, v in enumerate(dp)}
        d = exact_degree(len(dp), [tuple(re[v] for v in L[i]) for i in found], [S[i] for i in found])
        ok = len(dp) == 15 and d == 3
    check("A3 an explicit doily (15 points, 15 lines) with all lines outside a^perp, of degree 3", ok)
    check("A4 arithmetic: ceil(756/5) = 152, ceil(1071*152/756) = 216, ceil(23715*216/1071) = 4783, "
          "5*216 = 1080, ceil(86955*4783/23715) = 17538, 19635*216/1071 = 3960",
          -(-756 // 5) == 152 and -(-1071 * 152 // 756) == 216 and -(-23715 * 216 // 1071) == 4783
          and -(-86955 * 4783 // 23715) == 17538 and 19635 * 216 % 1071 == 0 and 19635 * 216 // 1071 == 3960)


if __name__ == "__main__":
    template_checks(); chain_checks(); small_degree_checks(); section_checks(); witness_checks(); rigidity_checks(); cone_checks(); structure_checks(); cascade_checks()
    import certify_asym                      # group X: blueprint/10 (spectral method, asymptotics)
    RESULTS.append(certify_asym.main())
    print(f"\n{sum(RESULTS)}/{len(RESULTS)} checks passed (the last one = all 18 asymptotic checks X1-X17)")
    sys.exit(0 if all(RESULTS) else 1)

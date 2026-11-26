"""Reduction to INDUCED line configurations (contexts = all lines of W(2n-1,2) inside the point set).
Signs are produced by adding, for each equation with rhs 1, two odd 'grid paths' (magic squares through
the equation's last chain line) instead of deleting/replacing lines.  Expected:
    degree(induced config) = min-unsat(H0, b) + (#equations with rhs 1)."""
import numpy as np, itertools
import reduction as R
from engine import Config, omega, from_str

T_P2 = ["IXIZ", "XIZI", "XXZZ"]
T_P3 = ["ZXIZ", "XZZI", "YYZZ"]

def ordered_triangle_split(H0, b):
    """Like reduction.triangle_split, but returns ordered triples so that the final chain pair of each
    of the three equations contains the original variable (prevents accidental aux lines)."""
    m, N = H0.shape
    rows, rhs, nxt = [], [], N
    for j in range(m):
        a, bb, c = np.nonzero(H0[j])[0]
        w1, w2, w3 = nxt, nxt + 1, nxt + 2; nxt += 3
        rows += [(w2, a, w1), (w3, bb, w2), (w1, c, w3)]
        rhs += [0, 0, int(b[j])]
    return rows, np.array(rhs, dtype=np.uint8), nxt

def build(H0, b, split=True):
    rows, b, N = ordered_triangle_split(H0, b)
    m = len(rows)
    B = R.Builder()
    blocks = []
    trip = []
    for v in range(N):
        qs = B.new_qubits(3); blocks.append(qs)
        trip.append([B.add_point(R._pauli_on(qs, s)) for s in R.COPY_LABELS[4]])
    last_lines = []
    for j in range(m):
        a_, bb, c = rows[j]
        seq = [trip[v][r] for r in range(4) for v in (a_, bb, c)]
        prev, acc = seq[0], B.pts[seq[0]]
        for k in range(1, len(seq) - 2):
            acc = R._add(acc, B.pts[seq[k]]); u = B.add_point(acc)
            B.ctx.append((prev, seq[k], u)); prev = u
        B.ctx.append((prev, seq[-2], seq[-1]))
        last_lines.append((prev, seq[-2], seq[-1], bb, c))
    for j in range(m):
        if not b[j]:
            continue
        u, s1, s2, v1, v2 = last_lines[j]
        A, Bz = B.pts[s1], B.pts[s2]                    # virtual qubit 1 <-> s1, qubit 2 <-> s2
        q1 = next(q for q in blocks[v1] if A.get(q, (0, 0))[1] == 1)
        q2 = next(q for q in blocks[v2] if Bz.get(q, (0, 0))[1] == 1)
        xi1, xi2 = {q1: (1, 0)}, {q2: (1, 0)}
        def embed(s, priv):
            d = {}
            x1, x2 = s[0] in "XY", s[1] in "XY"
            z1, z2 = s[0] in "ZY", s[1] in "ZY"
            if x1: d = R._add(d, xi1)
            if x2: d = R._add(d, xi2)
            if z1: d = R._add(d, A)
            if z2: d = R._add(d, Bz)
            return R._add(d, R._pauli_on(priv, s[2:]))
        for _ in range(2):                              # two odd paths
            priv = B.new_qubits(2)
            p2 = [B.add_point(embed(s, priv)) for s in T_P2]
            p3 = [B.add_point(embed(s, priv)) for s in T_P3]
            base = (s1, s2, u)                          # roles a, b, c = a+b
            B.ctx += [tuple(p2), tuple(p3)] + [(base[i], p2[i], p3[i]) for i in range(3)]
    return B.freeze()

def closure_lines(cfg):
    lab = np.stack(cfg.points)
    key = {r.tobytes(): i for i, r in enumerate(lab)}
    out = set()
    for i in range(len(lab)):
        for j in range(i + 1, len(lab)):
            k = key.get((lab[i] ^ lab[j]).tobytes())
            if k is not None and k > j and omega(lab[i], lab[j]) == 0:
                out.add((i, j, k))
    return out

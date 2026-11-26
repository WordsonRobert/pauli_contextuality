"""Reductions from MIN-UNSAT of XOR systems to the contextuality degree of Pauli configurations.

Two constructions:
  * general_hypergram(H0, b): contexts of size 9 (or 12 after a flip). Tripling + merge gadget.
  * line_configuration(H0, b): every context is a line {p, q, p+q} of W(2N-1, 2).
    Triangle-split (makes the system linear) + tripling + chains + line flip gadget.
In both, degree(output) == min_x |H0 x + b|.
"""
import numpy as np
from engine import Config, from_str

MS_ROWS = [["XI", "IX", "XX"], ["IZ", "ZI", "ZZ"], ["XZ", "ZX", "YY"]]


class Builder:
    """Accumulates points (as dicts qubit->(x,z)) on a growing register, then freezes."""

    def __init__(self):
        self.nq = 0
        self.pts = []          # list of dict q -> (x, z)
        self.ctx = []

    def new_qubits(self, k):
        q = list(range(self.nq, self.nq + k))
        self.nq += k
        return q

    def add_point(self, d):
        self.pts.append(d)
        return len(self.pts) - 1

    def freeze(self):
        N = self.nq
        arr = []
        for d in self.pts:
            v = np.zeros(2 * N, dtype=np.uint8)
            for q, (x, z) in d.items():
                v[q], v[N + q] = x, z
            arr.append(v)
        return Config(arr, self.ctx)


def _pauli_on(qs, s):
    return {q: (int(c in "XY"), int(c in "ZY")) for q, c in zip(qs, s) if c != "I"}


def _add(d1, d2):
    out = dict(d1)
    for q, (x, z) in d2.items():
        x0, z0 = out.get(q, (0, 0))
        out[q] = ((x0 + x) % 2, (z0 + z) % 2)
    return {q: v for q, v in out.items() if v != (0, 0)}


def _magic_square(B):
    """Add a fresh 2-qubit magic square; return (point index grid, list of its 6 contexts)."""
    qs = B.new_qubits(2)
    g = [[B.add_point(_pauli_on(qs, s)) for s in row] for row in MS_ROWS]
    rows = [tuple(r) for r in g]
    cols = [tuple(g[i][j] for i in range(3)) for j in range(3)]
    return g, rows + cols


COPY_LABELS = {3: ("ZZ", "ZI", "IZ"), 4: ("ZII", "IZI", "IIZ", "ZZZ")}


def _tripled_vars(B, N, copies=3):
    """Variable v -> `copies` Z-type points on private qubits whose labels sum to 0.
    copies=3: ZZ, ZI, IZ.  copies=4: ZII, IZI, IIZ, ZZZ (no three of them sum to 0)."""
    labs = COPY_LABELS[copies]
    trip = []
    for _ in range(N):
        qs = B.new_qubits(len(labs[0]))
        trip.append([B.add_point(_pauli_on(qs, s)) for s in labs])
    return trip


# ------------------------------------------------------------------ general hypergrams
def general_hypergram(H0, b):
    m, N = H0.shape
    B = Builder()
    trip = _tripled_vars(B, N)
    for j in range(m):
        ctx = [p for v in np.nonzero(H0[j])[0] for p in trip[v]]
        if b[j]:
            # merge gadget: union with one context of a fresh magic square, drop that context
            _, ms_ctx = _magic_square(B)
            ctx = ctx + list(ms_ctx[0])
            B.ctx.extend(ms_ctx[1:])
        B.ctx.append(tuple(ctx))
    return B.freeze()


# ------------------------------------------------------------------ line configurations
def triangle_split(H0, b):
    """Each 3-variable equation a+b+c=s  ->  a+w1+w2=0, b+w2+w3=0, c+w3+w1=s (fresh w's).
    Preserves min-unsat exactly; output is linear (no variable pair in two equations)."""
    m, N = H0.shape
    rows, rhs = [], []
    nxt = N
    for j in range(m):
        a, bb, c = np.nonzero(H0[j])[0]
        w1, w2, w3 = nxt, nxt + 1, nxt + 2
        nxt += 3
        rows += [(a, w1, w2), (bb, w2, w3), (c, w3, w1)]
        rhs += [0, 0, int(b[j])]
    H = np.zeros((len(rows), nxt), dtype=np.uint8)
    for r, t in enumerate(rows):
        H[r, list(t)] = 1
    return H, np.array(rhs, dtype=np.uint8)


def flip_line(B, line):
    """Line-preserving sign-flip gadget on line (a, b, c). Returns nothing; edits B in place.
    Removes line, adds a fresh magic square minus one of its lines h' = (a', b', c'),
    new points a'' = a+a', b'' = b+b', c'' = c+c', lines {a'',b'',c''} and {t, t', t''}."""
    B.ctx.remove(line)
    g, ms_ctx = _magic_square(B)
    hp = ms_ctx[0]
    B.ctx.extend(ms_ctx[1:])
    dbl = []
    for t, tp in zip(line, hp):
        t2 = B.add_point(_add(B.pts[t], B.pts[tp]))
        B.ctx.append((t, tp, t2))
        dbl.append(t2)
    B.ctx.append(tuple(dbl))


def line_configuration(H0, b, split=True, copies=3):
    if split:
        H0, b = triangle_split(H0, b)
    m, N = H0.shape
    B = Builder()
    trip = _tripled_vars(B, N, copies)
    for j in range(m):
        a, bb, c = np.nonzero(H0[j])[0]
        seq = [trip[v][r] for r in range(copies) for v in (a, bb, c)]
        # chain: {s0, s1, u1}, {u1, s2, u2}, ..., {u_{K-3}, s_{K-2}, s_{K-1}}
        prev = seq[0]
        acc = B.pts[seq[0]]
        lines = []
        for k in range(1, len(seq) - 2):
            acc = _add(acc, B.pts[seq[k]])
            u = B.add_point(acc)
            lines.append((prev, seq[k], u))
            prev = u
        last = (prev, seq[-2], seq[-1])
        lines.append(last)
        B.ctx.extend(lines)
        if b[j]:
            flip_line(B, last)
    return B.freeze()


# ------------------------------------------------------------------ arbitrary XOR systems
def xor_to_e3(G, t):
    """Arbitrary XOR system (rows of any length) -> exactly-3-variable system, same min-unsat.
    1. Variables occurring in rows of length < 3 are replaced by v1+v2+v3 everywhere.
    2. Rows of length L > 3 are chained:  s1+s2+w1=0, w1+s3+w2=0, ..., w_{L-3}+s_{L-1}+s_L=t."""
    G = np.asarray(G, dtype=np.uint8) % 2
    m, N = G.shape
    short = {v for j in range(m) if 0 < G[j].sum() < 3 for v in np.nonzero(G[j])[0]}
    nxt = N
    expand = {}
    for v in range(N):
        if v in short:
            expand[v] = [nxt, nxt + 1, nxt + 2]
            nxt += 3
        else:
            expand[v] = [v]
    rows, rhs = [], []
    for j in range(m):
        s = [u for v in np.nonzero(G[j])[0] for u in expand[v]]
        if not s:                         # empty row: constant constraint 0 = t_j
            raise ValueError("empty row")  # (contributes a fixed cost; excluded for simplicity)
        if len(s) == 3:
            rows.append(tuple(s)); rhs.append(int(t[j])); continue
        prev = s[0]
        for k in range(1, len(s) - 2):
            w = nxt; nxt += 1
            rows.append((prev, s[k], w)); rhs.append(0)
            prev = w
        rows.append((prev, s[-2], s[-1])); rhs.append(int(t[j]))
    H = np.zeros((len(rows), nxt), dtype=np.uint8)
    for r, tr in enumerate(rows):
        H[r, list(tr)] = 1
    return H, np.array(rhs, dtype=np.uint8)


# ------------------------------------------------------------------ compact labelling
def compactify(cfg, n_ms_regs_qubits, seed=0, extra=4):
    """Relabel a line configuration built with separate registers so that
    * all magic-square registers collapse onto ONE shared 2-qubit register, and
    * every other coordinate is replaced by q random kernel combinations (Z-type),
    with q ~ log2(#points). Signs are unchanged (proved in notes; asserted here).
    n_ms_regs_qubits: list of (q1, q2) register qubit pairs used by magic squares."""
    rng = np.random.default_rng(seed)
    L = np.stack(cfg.points)                     # |V| x 2Q, columns lie in ker H
    Q = cfg.n_qubits
    ms_x = np.zeros((len(L), 2), dtype=np.uint8)
    ms_z = np.zeros((len(L), 2), dtype=np.uint8)
    for (a, b) in n_ms_regs_qubits:
        ms_x ^= L[:, [a, b]]
        ms_z ^= L[:, [Q + a, Q + b]]
    q = int(np.ceil(np.log2(len(L) + 1)))
    while True:
        for _ in range(20):
            R = rng.integers(0, 2, (2 * Q, q)).astype(np.uint8)
            Z = (L.astype(np.int64) @ R % 2).astype(np.uint8)
            lab = np.concatenate([ms_x, np.zeros((len(L), q), np.uint8), ms_z, Z], axis=1)
            keys = {r.tobytes() for r in lab}
            if len(keys) == len(L) and lab.any(axis=1).all():
                new = Config(list(lab), cfg.contexts)
                assert new.signs == cfg.signs
                return new
        q += 1


def line_configuration_xor(G, t, compact=True, seed=0):
    """Arbitrary XOR system -> line configuration with degree == min_x |Gx + t|."""
    H3, b3 = xor_to_e3(G, t)
    Hs, bs = triangle_split(H3, b3)
    B = Builder()
    ms_regs = []
    orig = _magic_square

    def tracking_ms(B_):
        g, ctx = orig(B_)
        ms_regs.append((B_.nq - 2, B_.nq - 1))
        return g, ctx

    globals()["_magic_square"] = tracking_ms
    try:
        cfg = line_configuration(Hs, bs, split=False)
    finally:
        globals()["_magic_square"] = orig
    if compact:
        cfg = compactify(cfg, ms_regs, seed=seed)
    return cfg

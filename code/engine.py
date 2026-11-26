"""Core engine: Pauli configurations, context signs, exact contextuality degree.

A Pauli is a bit vector p = (x | z) of length 2n. Its canonical Hermitian operator is
P(p) = i^{x.z} X^x Z^z.  A configuration is a list of points (distinct Paulis) and a list
of contexts (tuples of point indices) whose operators pairwise commute and multiply to +-I.
"""
from __future__ import annotations
import itertools
import numpy as np
from ortools.sat.python import cp_model


# ---------------------------------------------------------------- Pauli algebra
def from_str(s: str) -> np.ndarray:
    n = len(s)
    v = np.zeros(2 * n, dtype=np.uint8)
    for i, c in enumerate(s):
        if c in "XY":
            v[i] = 1
        if c in "ZY":
            v[n + i] = 1
    return v


def to_str(v: np.ndarray) -> str:
    n = len(v) // 2
    return "".join("IXZY"[int(v[i]) + 2 * int(v[n + i])] for i in range(n))


def omega(p, q) -> int:
    n = len(p) // 2
    return int((p[:n] @ q[n:] + p[n:] @ q[:n]) % 2)


def product_sign(ops) -> int:
    """Return e in {0,1} with prod_j P(ops_j) = (-1)^e I. Raises if product is not +-I."""
    n = len(ops[0]) // 2
    k = 0
    x = np.zeros(n, dtype=np.int64)
    z = np.zeros(n, dtype=np.int64)
    for p in ops:
        x2, z2 = p[:n].astype(np.int64), p[n:].astype(np.int64)
        k += int(x2 @ z2) + 2 * int(z @ x2)          # i^{x2.z2} and reorder Z^z X^x2
        x, z = (x + x2) % 2, (z + z2) % 2
    if x.any() or z.any():
        raise ValueError("context product is not proportional to identity")
    k %= 4
    if k % 2:
        raise ValueError("product is +-iI (operators do not commute)")
    return k // 2


def tensor(p, q):
    """Pauli on registers (n1, n2) from p on n1 qubits and q on n2 qubits."""
    n1, n2 = len(p) // 2, len(q) // 2
    return np.concatenate([p[:n1], q[:n2], p[n1:], q[n2:]]).astype(np.uint8)


def zeros(n):
    return np.zeros(2 * n, dtype=np.uint8)


# ---------------------------------------------------------------- configurations
class Config:
    def __init__(self, points, contexts, check=True):
        self.points = [np.asarray(p, dtype=np.uint8) for p in points]
        self.contexts = [tuple(c) for c in contexts]
        if check:
            self.validate()
        self.signs = [product_sign([self.points[i] for i in c]) for c in self.contexts]

    @property
    def n_qubits(self):
        return len(self.points[0]) // 2

    def validate(self):
        keys = {p.tobytes() for p in self.points}
        assert len(keys) == len(self.points), "points not distinct"
        assert all(p.any() for p in self.points), "identity used as an observable"
        for c in self.contexts:
            for a, b in itertools.combinations(c, 2):
                assert omega(self.points[a], self.points[b]) == 0, "context not commuting"

    def incidence(self):
        H = np.zeros((len(self.contexts), len(self.points)), dtype=np.uint8)
        for r, c in enumerate(self.contexts):
            for v in c:
                H[r, v] ^= 1
        return H


# ---------------------------------------------------------------- degree
def min_unsat(H, e, time_limit=600, workers=8, hint=None):
    """min_x |Hx + e| over F2 (exact, CP-SAT). H: m x N 0/1, e: length m."""
    m, N = H.shape
    mdl = cp_model.CpModel()
    x = [mdl.NewBoolVar(f"x{i}") for i in range(N)]
    viol = [mdl.NewBoolVar(f"v{r}") for r in range(m)]
    for r in range(m):
        lits = [x[i] for i in np.nonzero(H[r])[0]]
        # sum(lits) + viol = e  (mod 2)  <=>  XOR(lits, viol, [not]) == True
        if e[r] == 1:
            mdl.AddBoolXOr(lits + [viol[r]])
        else:
            mdl.AddBoolXOr(lits + [viol[r].Not()])
    mdl.Minimize(sum(viol))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = time_limit
    s.parameters.num_workers = workers
    st = s.Solve(mdl)
    if st == cp_model.OPTIMAL:
        return int(round(s.ObjectiveValue())), True
    if st == cp_model.FEASIBLE:
        return int(round(s.ObjectiveValue())), False
    raise RuntimeError("solver failed")


def degree(cfg: Config, **kw):
    return min_unsat(cfg.incidence(), np.array(cfg.signs, dtype=np.uint8), **kw)


def brute_min_unsat(H, e):
    m, N = H.shape
    best = m
    for bits in itertools.product([0, 1], repeat=N):
        best = min(best, int(((H @ np.array(bits) + e) % 2).sum()))
    return best


# ---------------------------------------------------------------- F2 linear algebra
def rank_f2(M):
    M = M.copy() % 2
    r = 0
    rows, cols = M.shape
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i, c]), None)
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        r += 1
        if r == rows:
            break
    return r


def nullspace_f2(M):
    """Basis (rows) of {x : M x = 0}."""
    M = M.copy().astype(np.uint8) % 2
    rows, cols = M.shape
    pivots = []
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i, c]), None)
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        pivots.append(c)
        r += 1
        if r == rows:
            break
    free = [c for c in range(cols) if c not in pivots]
    basis = []
    for f in free:
        v = np.zeros(cols, dtype=np.uint8)
        v[f] = 1
        for i, pc in enumerate(pivots):
            if M[i, f]:
                v[pc] = 1
        basis.append(v)
    return np.array(basis, dtype=np.uint8).reshape(len(basis), cols)

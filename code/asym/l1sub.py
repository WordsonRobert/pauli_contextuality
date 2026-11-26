"""Alternating ascent restricted to an induced set X (default: symmetric Paulis = Q+(2N-1,2)), real or complex states.
Reports lambda_max vs the Cauchy-Schwarz cap sqrt(|X|(d-1)) and the violations given by the trace formula."""
import numpy as np, sys
from l1fast import setup, expectations, matrix
N = int(sys.argv[1]); trials = int(sys.argv[2]); real = (sys.argv[3] == 'real'); kind = sys.argv[4] if len(sys.argv) > 4 else 'Q+'
d, idx, ph = setup(N); rng = np.random.default_rng(5)
pc = np.vectorize(lambda v: bin(v).count('1'))
xz = pc(np.bitwise_and.outer(idx, idx))            # [x,z] -> |x&z|
if kind == 'Q+': mask = (xz % 2 == 0)
elif kind == 'Q-': mask = ((xz + (idx[:, None] & 1) + (idx[None, :] & 1)) % 2 == 0)
else: mask = np.ones((d, d), bool)
mask[0, 0] = False
n = int(mask.sum()); cap = np.sqrt(n * (d - 1))
# number of lines of the induced configuration: count via (sum over commuting pairs)/6 using trace with g=1 is not enough;
# use |L| = n * (points of the quotient) / 3 formula passed in via known counts
nL = {('Q+', 3): 105, ('Q+', 4): 1575, ('Q+', 5): 23715, ('Q+', 6): 365211, ('Q-', 4): 1071, ('Q-', 5): 19635, ('Q-', 3): 45}.get((kind, N))
best = -1
for t in range(trials):
    psi = rng.normal(size=d) + (0 if real else 1j * rng.normal(size=d)); psi = psi / np.linalg.norm(psi); val = -1
    for it in range(1000):
        E = expectations(psi.astype(complex), d, idx, ph)
        g = np.where(E >= 0, 1.0, -1.0) * mask
        M = matrix(g, d, idx, ph)
        if real: M = M.real
        w, V = np.linalg.eigh(M); psi = V[:, -1]
        if w[-1] <= val + 1e-10: break
        val = w[-1]
    if val > best + 1e-9:
        best = val; tr3 = np.sum(w**3)
        print(f'{kind} N={N} trial {t}: lambda_max {val:.5f} (cap {cap:.5f})  viol {nL/2 - tr3/(12*d) if nL else float("nan"):.2f}', flush=True)

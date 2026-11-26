"""Random-restart search for Pauli-covariant SIC fiducials in C^8 (= optimal W(5,2) assignments by ASY-4);
collect the distinct violated sets (= gauge classes = SICs) found."""
import numpy as np
from l1fast import setup, expectations, matrix
from product_witness import lines_and_signs
N = 3; d, idx, ph = setup(N); rng = np.random.default_rng(7)
a, b, s = lines_and_signs(N)
found = set(); hits = 0
for t in range(4000):
    psi = rng.normal(size=d) + 1j * rng.normal(size=d); psi /= np.linalg.norm(psi); val = -1
    for it in range(300):
        E = expectations(psi, d, idx, ph); g = np.where(E >= 0, 1, -1); g[0, 0] = 1
        M = matrix(g.astype(float) * (np.arange(d * d).reshape(d, d) != 0), d, idx, ph)
        w, V = np.linalg.eigh(M); psi = V[:, -1]
        if w[-1] <= val + 1e-10: break
        val = w[-1]
    if abs(val - 21) < 1e-6:
        hits += 1
        h = g.T.reshape(-1)          # h[x + d*z]  matches label a = x | z<<N
        viol = frozenset(np.nonzero(s * h[a] * h[b] * h[a ^ b] < 0)[0].tolist())
        assert len(viol) == 63
        found.add(viol)
print('runs reaching lambda_max = 21 (SIC):', hits, ' distinct violated sets:', len(found))

"""Monte Carlo check of ASY-5': average over Haar psi of (1/|L|) sum_l chi g g g with g = sign<P>, vs kappa(2^{N-2})."""
import numpy as np, sys
from l1fast import setup, expectations, matrix
for N, T in ((2, 40000), (3, 20000), (4, 8000), (5, 2000)):
    d, idx, ph = setup(N); rng = np.random.default_rng(N)
    nL = (4**N - 1) * (4**(N - 1) - 1) // 3; vals = []
    for _ in range(T):
        psi = rng.normal(size=d) + 1j * rng.normal(size=d); psi /= np.linalg.norm(psi)
        g = np.where(expectations(psi, d, idx, ph) >= 0, 1.0, -1.0); g[0, 0] = 0
        w = np.linalg.eigvalsh(matrix(g, d, idx, ph))
        vals.append(np.sum(w**3) / (6 * d) / nL)
    v = np.array(vals); print(f'N={N}: mean {v.mean():.5f} +- {2*v.std()/np.sqrt(T):.5f}', flush=True)

"""Search pure N-qubit states whose Pauli spectrum is flat on its support: every <P_a> in {0, +-gamma}.
Objective (Cieslinski 2026): f = sum_a e_a^2 (e_a^2 - gamma^2)^2-type; we use sum_a e_a^2 (e_a^2 - gamma^2)^2."""
import numpy as np, sys
from scipy.optimize import minimize
from l1fast import setup, expectations
N = int(sys.argv[1]); gam = float(sys.argv[2]); trials = int(sys.argv[3]); real = len(sys.argv) > 4 and sys.argv[4] == 'real'
d, idx, ph = setup(N); rng = np.random.default_rng(1)
def unpack(v):
    psi = v[:d] + (0 if real else 1j * v[d:]); return psi / np.linalg.norm(psi)
def f(v):
    E = expectations(unpack(v).astype(complex), d, idx, ph); E[0, 0] = 0
    return np.sum(E**2 * (E**2 - gam**2)**2)
best = None
for t in range(trials):
    v0 = rng.normal(size=d if real else 2 * d)
    r = minimize(f, v0, method='L-BFGS-B', options={'maxiter': 5000})
    if r.fun < 1e-7:
        E = expectations(unpack(r.x).astype(complex), d, idx, ph); E[0, 0] = 0
        S = np.argwhere(np.abs(E) > 0.05)
        print(f'trial {t}: f={r.fun:.2e} support size {len(S)}', flush=True)
        np.save(f'flat_N{N}_{t}.npy', unpack(r.x)); best = r.x
        if len(sys.argv) > 5: break
    else:
        print(f'trial {t}: f={r.fun:.3e}', flush=True)

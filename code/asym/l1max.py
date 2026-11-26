"""Numerical (non-rigorous) maximisation of the Pauli L1 norm  sum_{a!=0} |<psi|P_a|psi>|  = max_g lambda_max(M_g).
Alternating ascent: g <- sign(<P_a>), psi <- top eigenvector of M_g (monotone)."""
import numpy as np, sys
from spectral import pauli
N = int(sys.argv[1]); d = 2**N; rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
P = np.array([pauli(a, N) for a in range(1, 4**N)])
best = 0
for trial in range(int(sys.argv[3]) if len(sys.argv) > 3 else 200):
    psi = rng.normal(size=d) + 1j * rng.normal(size=d); psi /= np.linalg.norm(psi)
    val = -1
    for it in range(200):
        e = np.einsum('i,aij,j->a', psi.conj(), P, psi).real
        g = np.where(e >= 0, 1.0, -1.0)
        M = np.einsum('a,aij->ij', g, P)
        w, V = np.linalg.eigh(M); psi = V[:, -1]
        if w[-1] <= val + 1e-12: break
        val = w[-1]
    if val > best:
        best = val; tr3 = np.sum(w**3)
        print(f'trial {trial}: L1 = {val:.6f}  tr M^3 = {tr3:.1f}  -> violations {(4**N-1)*(4**(N-1)-1)/6 - tr3/(12*d):.2f}', flush=True)
print('Cauchy-Schwarz cap', np.sqrt((4**N-1)*(2**N-1)))

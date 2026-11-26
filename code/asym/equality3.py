"""ASY-4: the W(5,2) witness (63 violations) has spectrum {21^1, (-3)^7}: equality in the spectral bound,
so g(a) = 3<psi|P_a|psi> for a 3-qubit state psi with |<psi|P_a|psi>|^2 = 1/9 for all a != 0 (a Hoggar SIC fiducial)."""
import sys, os, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'certificates'))
import certify as C
from spectral import pauli

def vec_to_int(p, N):
    return sum(int(p[i]) << i for i in range(N)) | sum(int(p[N + i]) << (N + i) for i in range(N))

for N, fn in ((3, 'witness_W5_2.txt'), (4, 'witness_W7_2.txt')):
    pts, L, S = C.geometry('W', N)
    x = [int(t) for t in open(os.path.join(os.path.dirname(C.__file__), fn))]
    M = sum((1 - 2 * xi) * pauli(vec_to_int(p, N), N) for p, xi in zip(pts, x))
    ev = np.linalg.eigvalsh(M)
    v = C.violations(x, L, S)
    tr3 = float(np.sum(ev**3))
    print(f'N={N}: violations {v}; |L|/2 - tr(M^3)/(12 d) = {len(L)/2 - tr3/(12*2**N):.6f}')
    print('   spectrum', np.round(ev, 4))
    if N == 3:
        w, V = np.linalg.eigh(M); psi = V[:, -1]
        exps = [abs(np.vdot(psi, pauli(vec_to_int(p, N), N) @ psi))**2 for p in pts]
        print('   top eigvec: min/max |<P>|^2 =', min(exps), max(exps), '(1/9 =', 1/9, ')')

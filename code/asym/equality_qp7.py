"""ASY-4b: deg Q+(7,2) = 315.  The spectral bound gives >= 315 (quadric_bounds.py); a tabu witness gives 315.
Equality forces spectrum {45^1, (-3)^15}: M = 48|psi><psi| - 3I with a REAL 4-qubit state psi satisfying
|<psi|P|psi>| = 1/3 on all 135 symmetric non-identity Paulis (and 0 on antisymmetric ones)."""
import sys, os, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'certificates'))
import certify as C
from spectral import pauli
N = 4; fn = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'certificates', 'witness_Qp7_2.txt')
pts, L, S = C.geometry('Q+', N); x = [int(t) for t in open(fn)]
v = C.violations(x, L, S)
toint = lambda p: sum(int(p[i]) << i for i in range(N)) | sum(int(p[N + i]) << (N + i) for i in range(N))
M = sum((1 - 2 * xi) * pauli(toint(p), N) for p, xi in zip(pts, x))
w, V = np.linalg.eigh(M); psi = V[:, -1]
print('violations', v, 'spectrum', np.round(w, 6))
ph = psi * np.exp(-1j * np.angle(psi[np.argmax(abs(psi))]))
print('psi real up to phase:', np.allclose(ph.imag, 0, atol=1e-9))
sym = [abs(np.vdot(psi, pauli(toint(p), N) @ psi)) for p in pts]
anti = [abs(np.vdot(psi, pauli(a, N) @ psi)) for a in range(1, 256) if bin((a & 15) & (a >> 4)).count('1') % 2]
print('|<P>| on symmetric: min %.6f max %.6f; on antisymmetric max %.2e' % (min(sym), max(sym), max(anti)))

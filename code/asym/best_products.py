"""Best product constructions from certified block patterns: tau_1=10, tau_3=1324 (Hoggar), tau_4=13996, tau_5=147052
(blocks from certificates/witness_W7_2.txt, witness_W9_2.txt).  Verifies tau_k by counting and certifies products by
direct counting for N<=7; for larger N the value follows from Lemma ASY-6 (multiplicativity)."""
import numpy as np, os, sys
from product_witness import lines_and_signs, tensor_h, single_h, C

def block_h(N, fn):
    pts, L, S = C.geometry('W', N); x = [int(t) for t in open(os.path.join(os.path.dirname(C.__file__), fn))]
    h = np.ones(4**N, dtype=np.int64)
    for p, xi in zip(pts, x):
        a = sum(int(p[i]) << i for i in range(N)) | sum(int(p[N + i]) << (N + i) for i in range(N))
        h[a] = 1 - 2 * xi
    return h

H = {1: single_h(), 3: block_h(3, 'witness_W5_2.txt'), 4: block_h(4, 'witness_W7_2.txt'), 5: block_h(5, 'witness_W9_2.txt')}
tau = {}
for k, h in H.items():
    a, b, s = lines_and_signs(k); v = int(np.sum(s * h[a] * h[b] * h[a ^ b] < 0)) if k > 1 else 0
    nL = len(a); tau[k] = round(12 * (nL / 2 - v) + 3 * 4**k - 2)
print('tau =', tau)
best = {0: (1, [])}
for N in range(1, 31):
    best[N] = max(((best[N - k][0] * tau[k], best[N - k][1] + [k]) for k in tau if k <= N), key=lambda t: t[0])
def L(N): return (4**N - 1) * (4**(N - 1) - 1) // 3
for N in range(2, 21):
    t, comp = best[N]; up = L(N) // 2 - (t - 3 * 4**N + 2 - 6 * (L(N) % 2)) // 12 if False else None
    from fractions import Fraction
    upF = Fraction(L(N), 2) - Fraction(t - 3 * 4**N + 2, 12)
    print(f'N={N:2d} blocks {sorted(comp)} deg <= {upF} rho <= {float(upF / L(N)):.6f}')
    if N <= 7 and '--count' in sys.argv:
        hh = tensor_h([(k, H[k]) for k in comp]); a, b, s = lines_and_signs(N)
        v = int(np.sum(s * hh[a] * hh[b] * hh[a ^ b] < 0)); assert v == upF, (v, upF); print('      counted OK')

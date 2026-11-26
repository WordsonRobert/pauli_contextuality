"""ASY-8: strict growth rho_3 < rho_4 < ... < rho_11, from
   upper bounds  rho_N <= U_N  (explicit product assignments; counted for N<=7, multiplicativity ASY-6 beyond)
   lower bounds  rho_N >= ceil(ASY-3)/|L_N|.
Also checks the closed form for the number of negative lines, (16^N + 4^N - 2*10^N)/24, against direct counts N<=7."""
from fractions import Fraction as Fr
from mpmath import mp, mpf, sqrt, ceil
import numpy as np
from product_witness import lines_and_signs
mp.dps = 60
def L(N): return (4**N - 1) * (4**(N - 1) - 1) // 3
def low(N):
    q = mpf(4**N - 1); return int(ceil(mpf(L(N)) / 2 - q**1.5 * (2**N - 2) / (12 * sqrt(2**N - 1)) - mpf('1e-40')))
tau = {1: 10, 3: 1324, 4: 13996, 5: 147052}
best = {0: 1}
for N in range(1, 16): best[N] = max(best[N - k] * tau[k] for k in tau if k <= N)
def up(N): return Fr(L(N), 2) - Fr(best[N] - 3 * 4**N + 2, 12)
for N in range(2, 8):
    a, b, s = lines_and_signs(N); neg = int(np.sum(s < 0))
    assert neg * 24 == 16**N + 4**N - 2 * 10**N, N
print('negative-line closed form verified N=2..7')
known_up = {4: 1575, 5: 31479}
for N in range(3, 11):
    u = Fr(min(up(N), known_up.get(N, 10**30)), L(N)); l1 = Fr(low(N + 1), L(N + 1))
    print(f'rho_{N} <= {float(u):.6f} < {float(l1):.6f} <= rho_{N+1} : {u < l1}')
    assert u < l1
print('strict chain rho_3 < ... < rho_11: PASS')

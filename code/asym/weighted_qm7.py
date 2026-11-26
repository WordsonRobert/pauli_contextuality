"""Weighted spectral bounds for Q-(7,2), split by a non-singular point a:
   P = Q- ∩ a^perp (63 points; its 315 lines form the parabolic section Q(6,2) ≅ W(5,2), deg 63),
   O = the other 56 points; the 756 lines of O_a have exactly one point in P (weight product t), lines of Q(6,2) weight t^3.
   Weighted ASY-2 (weights w on points, CS with weights): sum_l w_l chi g g g <= (Lam F - F^2/(d Lam))/(6 d) with
   F = d * sum w^2, Lam = sqrt((d-1) sum w^2).  Hence t*V_O + t^3*V_P >= (t*756 + t^3*315 - B(t))/2.
   Combine with V_P >= 63, V_O >= 152 (cascade) and LP-minimise V_O + V_P."""
import numpy as np
from scipy.optimize import linprog
d = 16; LO, LP = 756, 315
A, b = [], []
for t in np.concatenate([np.linspace(0.01, 1, 200), np.linspace(1, 6, 300)]):
    W = 56 + 63 * t * t; F = d * W; Lam = np.sqrt((d - 1) * W)
    B = (Lam * F - F * F / (d * Lam)) / (6 * d)
    A.append([-t, -t**3]); b.append(-(t * LO + t**3 * LP - B) / 2)
for lo in ((0, 0), (152, 63)):
    r = linprog([1, 1], A_ub=A, b_ub=b, bounds=[(lo[0], LO), (lo[1], LP)])
    print(f'with V_O>={lo[0]}, V_P>={lo[1]}: min V_O+V_P = {r.fun:.2f} (V_O={r.x[0]:.1f}, V_P={r.x[1]:.1f})')

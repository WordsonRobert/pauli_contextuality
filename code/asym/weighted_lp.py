"""Weighted spectral bounds on W(7,2) split by an elliptic quadric Q-(7,2):
   lines of W(7,2) = L1 (1071 lines inside Q-) + L2 (4284 lines with 1 singular + 2 nonsingular points).
   Weights w = 1 on Q- (119 pts), t on the 136 nonsingular points: for any assignment,
        V1 + t^2 V2 >= ( |L1| + t^2 |L2| - S(t) ) / 2,   S(t) = Wt^{3/2}(d-2)/(6 sqrt(d-1)),  Wt = 119 + 136 t^2.
   Combined with V1 >= 216 (GEO-2), V2 >= 0: minimise V1 + V2 by LP over a grid of t."""
import numpy as np
from scipy.optimize import linprog
d = 16; L1, L2 = 1071, 5355 - 1071
ts = np.linspace(0, 3, 601)
A, b = [], []
for t in ts:
    W = 119 + 136 * t * t; S = W**1.5 * (d - 2) / (6 * np.sqrt(d - 1))
    A.append([-1, -t * t]); b.append(-(L1 + t * t * L2 - S) / 2)
for v1lb in (0, 216, 315):
    res = linprog([1, 1], A_ub=A, b_ub=b, bounds=[(v1lb, L1), (0, L2)])
    print(f'V1 >= {v1lb}: min V1+V2 = {res.fun:.2f}  at V1={res.x[0]:.1f}, V2={res.x[1]:.1f}')

from mpmath import mp, mpf, pslq
from fractions import Fraction
import kendall
mp.dps = 45
for k in (1, 2, 4, 8):
    kap = kendall.kappa(k)
    best = None
    for e in range(1, 80):
        num = kap * mpf(2)**e
        if abs(num - round(num)) < mpf(10)**-25:
            best = Fraction(int(round(num)), 2**e); break
    print(k, mp.nstr(kap, 35), best)

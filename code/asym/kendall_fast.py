"""kappa(k) in float64 (scipy), Gauss-Legendre on scaled windows; validated against the exact dyadic values for k<=8."""
import numpy as np
from scipy.special import betainc, gammaln
from numpy.polynomial.legendre import leggauss
def kappa(k, n=4000, W=14.0):
    x, w = leggauss(n)
    # r-grid on [0, rmax], rmax = min(1, W/sqrt(2k)); density of R
    rmax = min(1.0, W / np.sqrt(2 * k)); r = (x + 1) / 2 * rmax; wr = w * rmax / 2
    lfR = (k - 1) * np.log1p(-r * r) - (2 * k - 2) * np.log(2) - (2 * gammaln(k) - gammaln(2 * k))
    fR = np.exp(lfR) * wr
    vmax = min(0.5, W / np.sqrt(16 * k)); v = 0.5 + (x + 1) / 2 * vmax; wv = w * vmax / 2
    lfV = (2 * k - 1) * (np.log(v) + np.log1p(-v)) - (2 * gammaln(2 * k) - gammaln(4 * k))
    fV = np.exp(lfV) * wv
    c = (1 - v) / v                                   # c in (0,1]
    FR = 2 * betainc(k, k, (1 + np.outer(c, r)) / 2) - 1   # P(R <= c r)
    H = FR @ fR
    return 2 * np.sum(fV * (1 - 2 * H))
exact = {1: 1 / 2, 2: 23 / 64, 4: 133519 / 2**19, 8: 50649838284767 / 2**48}
for k, e in exact.items(): print('check k', k, kappa(k), e, abs(kappa(k) - e))
lim = (2 / np.pi)**1.5
prev = None
for N in range(3, 31):
    k = 2**(N - 2); kp = kappa(k); val = kp * np.sqrt(k)
    print(f'N={N:2d} kappa*sqrt(k) = {val:.9f}  (minus limit {val - lim:+.3e})' + ('' if prev is None or val < prev else '  NOT DECREASING'))
    prev = val

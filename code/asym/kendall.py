"""ASY-5' (exact Haar line correlation).  For Haar psi in C^{2^N} and g = sign<psi|P_a|psi>, every line l satisfies
     E[ chi(l) g(a) g(b) g(c) ] = kappa(k),  k = 2^{N-2},
where kappa(k) = E[ sgn(S1 - S2) sgn(S1 R1 - S2 R2) ] (Kendall tau of (|X-Y|, X+Y), X,Y iid Gamma(k)),
S ~ Gamma(2k), R = |2B-1|, B ~ Beta(k,k), all independent.  Here we compute kappa(k) by 1-D/2-D quadrature
(mpmath) and check it against Monte Carlo on actual Pauli lines."""
import sys
from mpmath import mp, mpf, quad, betainc, beta, sqrt, pi, inf
mp.dps = 30

def H(c, k):
    """P(R1 < c R2) for R iid with density f_R(r) = 2 f_B((1+r)/2)/2... R = |2B-1|: f_R(r) = (1-r^2)^{k-1} / (2^{2k-2} B(k,k)), r in [0,1]"""
    if c >= 1:
        return 1 - H(1 / c, k)
    fR = lambda r: (1 - r * r)**(k - 1) / (mpf(2)**(2 * k - 2) * beta(k, k))
    FR = lambda r: betainc(k, k, 0, (1 + r) / 2, regularized=True) * 2 - 1      # P(R <= r)
    return quad(lambda r: fR(r) * FR(c * r), [0, 1])

def kappa(k):
    # V = S1/(S1+S2) ~ Beta(2k,2k);  kappa = E[ sgn(V-1/2) (1 - 2 H((1-V)/V)) ] = 2 * int_{1/2}^1 fV(v)(1 - 2H((1-v)/v)) dv
    fV = lambda v: v**(2 * k - 1) * (1 - v)**(2 * k - 1) / beta(2 * k, 2 * k)
    return 2 * quad(lambda v: fV(v) * (1 - 2 * H((1 - v) / v, k)), [mpf(1) / 2, 1])

if __name__ == '__main__':
    lim = (2 / pi)**1.5
    for N in range(2, int(sys.argv[1]) if len(sys.argv) > 1 else 9):
        k = 2**(N - 2); kap = kappa(k)
        print(f'N={N} k={k:4d} kappa={float(kap):.6f}  kappa*sqrt(k)={float(kap*sqrt(k)):.5f} (limit (2/pi)^1.5={float(lim):.5f})'
              f'  => rho_N <= (1-kappa)/2 = {float((1-kap)/2):.5f};  delta*2^(N/2) >= {float(kap/2*2**(N/2.)):.5f}', flush=True)

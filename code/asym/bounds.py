"""Rigorous two-sided bounds on deg W(2N-1,2) and rho_N from the spectral formula (blueprint/10)."""
from mpmath import mp, mpf, sqrt, binomial, ceil, floor
mp.dps = 50

def L(N): return (4**N - 1) * (4**(N - 1) - 1) // 3

def lower(N):
    # deg >= |L|/2 - (4^N-1)^{3/2}(2^N-2) / (12 sqrt(2^N-1))      [ASY-3]
    q = mpf(4**N - 1)
    return mpf(L(N)) / 2 - q**1.5 * (2**N - 2) / (12 * sqrt(2**N - 1))

def upper_random(N):
    # deg <= |L|/2 - (lam^3 - (F-lam^2)^{3/2})/(12 d), lam = (4^N-1) C(2m,m)/4^m, m=2^{N-1}  [ASY-5]
    d = 2**N; m = d // 2; F = mpf(d * (4**N - 1))
    lam = (4**N - 1) * binomial(2 * m, m) / mpf(4)**m
    s = (lam**3 - (F - lam**2)**1.5) / d
    return mpf(L(N)) / 2 - s / 12

def upper_product(N, blocks):
    # product of single-qubit magic signs (tau_1 = 10) and Hoggar blocks (tau_3 = 1324) [ASY-6]
    t = 1
    for b in blocks: t *= {1: 10, 3: 1324}[b]
    S = t - 3 * 4**N + 2
    return mpf(L(N)) / 2 - mpf(S) / 12

if __name__ == '__main__':
    print(f"{'N':>2} {'|L|':>14} {'lower':>14} {'upper(best)':>14} {'rho_low':>9} {'rho_up':>9} {'(1/2-rho_up)2^(N/2)':>10} {'(1/2-rho_low)2^(N/2)':>10}")
    for N in range(2, 16):
        lo = max(mpf(0), ceil(lower(N) - mpf('1e-30')))
        cands = [upper_random(N)]
        for k3 in range(N // 3 + 1):
            cands.append(upper_product(N, [3] * k3 + [1] * (N - 3 * k3)))
        up = floor(min(cands) + mpf('1e-30'))
        LN = L(N)
        print(f"{N:>2} {LN:>14} {int(lo):>14} {int(up):>14} {float(lo/LN):9.5f} {float(up/LN):9.5f} {float((0.5-up/LN)*2**(N/2)):10.4f} {float((0.5-lo/LN)*2**(N/2)):10.4f}")

"""ASY-2 applied to the quadric families Q+(2N-1,2), Q-(2N-1,2) (induced configurations of N-qubit Paulis)."""
from mpmath import mp, mpf, sqrt, ceil
mp.dps = 40
def npts(kind, N): return (2**N - 1) * (2**(N - 1) + 1) if kind == '+' else (2**N + 1) * (2**(N - 1) - 1)
def nlines(kind, N): return npts(kind, N) * npts(kind, N - 1) // 3
def lower(kind, N):
    d = 2**N; X = npts(kind, N); F = mpf(d * X); Lam = sqrt(mpf(X) * (d - 1))
    return mpf(nlines(kind, N)) / 2 - (Lam * F - F**2 / (d * Lam)) / (12 * d)
known = {('+', 3): (21, 21), ('-', 3): (9, 9), ('-', 4): (216, 315), ('+', 4): (None, None), ('+', 5): (4783, 6975), ('-', 5): (3960, 7087)}
for kind in '+-':
    for N in range(3, 11):
        lo = lower(kind, N); L = nlines(kind, N)
        print(f'Q{kind}({2*N-1},2): points {npts(kind,N):>7} lines {L:>12}  spectral lower {int(max(0, ceil(lo))):>11}  '
              f'rho >= {float(max(0, ceil(lo)) / L):.4f}  (1/2-rho_low)*2^(N/2) = {float((0.5 - lo / L) * 2**(N / 2)):.4f}  prior {known.get((kind, N), "")}')

"""Checks for ASY-5 (Haar construction) and ASY-7 (jump windows), N = 2..80, exact arithmetic in mpmath.
  w_m = C(2m,m)/4^m = E|<psi|P|psi>| (Haar, d = 2m);  Wallis: 1/sqrt(pi(m+1/2)) <= w_m <= 1/sqrt(pi(m+1/4)).
  c_N^2 = (4^N-1) w_m^2 / 2^N ;  phi(c) = c^3 - (1-c^2)^{3/2} ;  delta_N := 1/2 - rho_N.
  Lower bound on delta (ASY-5):  delta_N >= phi(c_N) sqrt(2^N (4^N-1)) / (4^N - 4)   (exact form, before simplification)
  Upper bound on delta (ASY-3):  delta_N <= sqrt(4^N-1)(2^N-2) / ((4^N-4) sqrt(2^N-1)) <= 2^{-N/2}."""
from mpmath import mp, mpf, sqrt, binomial, pi
mp.dps = 60
ok = True
for N in range(2, 81):
    d = 2**N; m = d // 2; w = binomial(2 * m, m) / mpf(4)**m
    wal_lo, wal_hi = 1 / sqrt(pi * (m + mpf(1) / 2)), 1 / sqrt(pi * (m + mpf(1) / 4))
    ok &= wal_lo <= w <= wal_hi
    c = sqrt((4**N - 1) * w**2 / d); phi = c**3 - (1 - c**2)**1.5
    dlo = phi * sqrt(mpf(d) * (4**N - 1)) / (4**N - 4)
    dhi = sqrt(mpf(4**N - 1)) * (d - 2) / ((4**N - 4) * sqrt(mpf(d - 1)))
    ok &= dhi <= 2**(-mpf(N) / 2)
    if N >= 6: ok &= dlo * 2**(mpf(N) / 2) >= mpf('0.2679')
    if N in (2, 3, 4, 5, 6, 8, 10, 20, 40, 80):
        print(f'N={N:2d} c={float(c):.5f} phi={float(phi):.5f}  delta*2^(N/2) in [{float(dlo*2**(N/2)):.5f}, {float(dhi*2**(N/2)):.5f}]')
# jump windows: rho_{N+4} >= 1/2 - dhi(N+4) > 1/2 - dlo(N) >= rho_N  for N >= 6
for N in range(6, 77):
    d = 2**N; m = d // 2; w = binomial(2 * m, m) / mpf(4)**m; c = sqrt((4**N - 1) * w**2 / d)
    dlo = (c**3 - (1 - c**2)**1.5) * sqrt(mpf(d) * (4**N - 1)) / (4**N - 4)
    M = N + 4; dhi4 = sqrt(mpf(4**M - 1)) * (2**M - 2) / ((4**M - 4) * sqrt(mpf(2**M - 1)))
    ok &= dhi4 < dlo
print('phi limit sqrt(2/pi):', float(sqrt(2 / pi)**3 - (1 - 2 / pi)**1.5))
print('ALL CHECKS', 'PASS' if ok else 'FAIL')

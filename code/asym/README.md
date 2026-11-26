# code/asym — spectral method (blueprint/10_asymptotics.md)

| script | what it does | blueprint |
|---|---|---|
| spectral.py | dense Pauli matrices; verifies the trace formula on W, Q+, Q- for N = 2,3,4 | ASY-1 |
| bounds.py | rigorous lower (ASY-3) and upper (Haar ASY-5, products ASY-6) bounds, N = 2..15 | ASY-3/5/6 |
| equality3.py | spectrum of the W(5,2) and W(7,2) witnesses; Hoggar flatness of the N=3 top eigenvector | ASY-4 |
| equality_qp7.py | deg Q+(7,2) = 315: spectrum {45,(-3)^15}, real flat state | ASY-4b |
| w5_orbit.py | Sp(6,2)-orbit of the optimal W(5,2) violated set: 120, stabiliser 12096 | ASY-4 |
| w5_sics.py | 4000 random restarts: every SIC found is one of the same 120 | ASY-4 |
| product_witness.py | tensor-product assignments; violations COUNTED line by line, N <= 7 (`--big` for 7) | ASY-6 |
| best_products.py | best block partitions (tau_1, tau_3, tau_4, tau_5); `--count` certifies N <= 7 | ASY-6 |
| chain.py | strict chain rho_3 < ... < rho_11; negative-line closed form N <= 7 | ASY-6/7 |
| haar_constants.py | Beta/Wallis constants, delta*2^{N/2} bounds, window-4 inequality, N = 2..80 | ASY-5/7 |
| quadric_bounds.py | ASY-2 for Q+/Q- (2N-1,2), N = 3..10 | ASY-9 |
| l1max.py, l1fast.py | alternating ascent psi -> g = sign<P> -> top eigenvector (CONJ-3 evidence); l1fast uses Walsh–Hadamard transforms and handles N <= 8 | CONJ-3 |
| kendall.py, kendall_exact.py | kappa(k) (mpmath); exact dyadic values kappa(1,2,4,8) | ASY-5' |
| kendall_fast.py | kappa(k) sqrt(k) for N <= 19 (float64 Gauss–Legendre; unreliable beyond ~19) | ASY-5', CONJ-4 |
| kendall_mc.py | Monte Carlo of the measure-and-assign strategy on Pauli lines, N = 2..5 | ASY-5' |
| l1sub.py | ascent restricted to quadrics (real/complex states) | CONJ-3 |
| weighted_lp.py | weighted spectral bounds (Q- / complement split) + LP: no gain | ASY-2 remark |
| flat_search.py, flat_analyze.py | search pure states Pauli-flat on their support; analyse support, lines, tightness (TIGHT-1) | TIGHT |
| weighted_qm7.py | two-class weighted spectral LP on Q-(7,2): no gain over 215 | NEG-1 |
| fast_N*.log, l1_N6.log | ascent logs for N = 6, 7, 8 (worse than products; see CONJ-3 caveat) | |

Requires numpy and mpmath (`pip install mpmath`). The standalone checks are in `certificates/certify_asym.py`
(numpy + stdlib only).

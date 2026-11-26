#!/usr/bin/env python3
"""Checks X1-X17 for blueprint/10_asymptotics.md (spectral method, limit 1/2, jumps).

Standalone: numpy + Python standard library only (exact integer / Fraction arithmetic wherever a bound is claimed).
Independent re-implementation: Pauli matrices built from scratch, lines enumerated from scratch, signs computed from
matrix products (X1, X4, X6) and from the integer phase formula (X8-X10); the two are compared in X2.
"""
import os, sys, math, itertools, random
from fractions import Fraction as Fr
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RES = []


def check(name, ok, detail=""):
    RES.append(bool(ok))
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))


# ------------------------------------------------------------------ Pauli matrices, labels a = x | (z << N)
I2 = np.eye(2, dtype=complex); SX = np.array([[0, 1], [1, 0]], complex); SZ = np.diag([1.0 + 0j, -1.0])
SY = 1j * SX @ SZ          # i X Z = Y (Hermitian); canonical P = i^{x.z} X^x Z^z


def pmat(a, N):
    M = np.array([[1.0 + 0j]])
    for i in range(N):
        x, z = (a >> i) & 1, (a >> (N + i)) & 1
        M = np.kron([I2, SX, SZ, SY][x + 2 * z], M)        # qubit i <-> bit i (order irrelevant for traces)
    return M


def pc(v): return bin(v).count("1")
def omega(a, b, N): m = (1 << N) - 1; return (pc(a & m & (b >> N)) + pc((a >> N) & b & m)) & 1


def chi_int(a, b, N):
    """chi(a,b) for commuting a,b from the integer phase formula: P_a P_b = i^k P_{a+b}."""
    m = (1 << N) - 1; c = a ^ b
    k = (pc(a & m & (a >> N)) + pc(b & m & (b >> N)) - pc(c & m & (c >> N)) + 2 * pc((a >> N) & b & m)) % 4
    assert k in (0, 2)
    return 1 if k == 0 else -1


def lines(X, N):
    S = set(X)
    return [(a, b, a ^ b) for a in X for b in X if a < b < (a ^ b) and (a ^ b) in S and omega(a, b, N) == 0]


def is_sym(a, N): return pc(a & ((1 << N) - 1) & (a >> N)) % 2 == 0


def L_W(N): return (4**N - 1) * (4**(N - 1) - 1) // 3


def isqrt_ceil(n): r = math.isqrt(n); return r if r * r == n else r + 1


# ------------------------------------------------------------------ exact form of the ASY-2 bound
def spectral_lower_ceiling(nL, n, N):
    """ceil( nL/2 - (Lam F - F^2/(d Lam))/(12 d) ), Lam = sqrt(n(d-1)), F = d n.
    = ceil( nL/2 - n (Lam^2 - n)/(12 Lam) ) = ceil( nL/2 - n^{3/2}(d-2)/(12 sqrt(d-1)) ) ... computed exactly:
    we need the least integer D with D >= nL/2 - n*(n(d-1)-n)/(12*sqrt(n(d-1))). Put T = n*n*(d-2)/12, R = n(d-1):
    bound = nL/2 - T/sqrt(R). D works iff (nL/2 - D) <= T/sqrt(R) fails ... we search D directly with exact squares."""
    d = 2**N; T = Fr(n * n * (d - 2), 12); R = n * (d - 1)
    # bound B = nL/2 - T/sqrt(R).  Smallest integer D >= B:  D >= B  <=>  nL/2 - D <= T/sqrt(R)
    #   <=>  (nL/2 - D) <= 0  or  (nL/2 - D)^2 * R <= T^2
    D = 0
    lo, hi = 0, nL
    while lo < hi:                      # binary search the least D satisfying the predicate (monotone in D)
        mid = (lo + hi) // 2; t = Fr(nL, 2) - mid
        ok = t <= 0 or t * t * R <= T * T
        if ok: hi = mid
        else: lo = mid + 1
    return lo


def main():
    rng = random.Random(1)
    # X1 trace formula on W, Q+, Q- for N = 2, 3, 4
    ok = True
    for N in (2, 3, 4):
        full = list(range(1, 4**N)); m = (1 << N) - 1
        qm = [a for a in full if (pc(a & m & (a >> N)) + (a & 1) + ((a >> N) & 1)) % 2 == 0]
        for X in (full, [a for a in full if is_sym(a, N)], qm):
            Pm = {a: pmat(a, N) for a in X}; Ls = lines(X, N)
            ch = {l: (1 if np.allclose(Pm[l[0]] @ Pm[l[1]] @ Pm[l[2]], np.eye(2**N)) else -1) for l in Ls}
            for _ in range(2):
                g = {a: rng.choice((-1, 1)) for a in X}
                lhs = sum(ch[l] * g[l[0]] * g[l[1]] * g[l[2]] for l in Ls)
                M = sum(g[a] * Pm[a] for a in X)
                ok &= abs(lhs - np.trace(M @ M @ M).real / (6 * 2**N)) < 1e-6
    check("X1 trace formula sum_l chi g g g = tr(M^3)/(6d) on W, Q+, Q- (N=2,3,4), random g", ok)

    # X2 integer phase formula agrees with matrices (all lines of W(7,2))
    N = 4; Pm = {a: pmat(a, N) for a in range(1, 256)}
    ok = all(np.allclose(Pm[a] @ Pm[b], chi_int(a, b, N) * Pm[a ^ b]) for a, b, c in lines(list(range(1, 256)), N))
    check("X2 integer phase formula chi(a,b) = matrix sign on all 5355 lines of W(7,2)", ok)

    # X3 the ASY-3 bound values (exact arithmetic)
    vals = {N: spectral_lower_ceiling(L_W(N), 4**N - 1, N) for N in range(2, 9)}
    want = {2: 2, 3: 63, 4: 1451, 5: 28786, 6: 527621, 7: 9227609, 8: 156705492}
    check("X3 ASY-3 lower bounds deg W(2N-1,2) >= 2, 63, 1451, 28786, 527621, 9227609, 156705492 (N=2..8)",
          vals == want, str(vals))

    # X4 W(5,2) witness: 63 violations, spectrum {21, -3^7}, top eigenvector Hoggar-flat
    N = 3; pts = list(range(1, 64))
    W5 = __import__("certify").geometry("W", 3)
    x = [int(t) for t in open(os.path.join(HERE, "witness_W5_2.txt"))]
    lab = [sum(int(p[i]) << i for i in range(3)) | sum(int(p[3 + i]) << (3 + i) for i in range(3)) for p in W5[0]]
    M = sum((1 - 2 * xi) * pmat(a, 3) for a, xi in zip(lab, x))
    w, V = np.linalg.eigh(M); psi = V[:, -1]
    flat = [abs(np.vdot(psi, pmat(a, 3) @ psi))**2 for a in pts]
    check("X4 W(5,2) witness: spectrum {21^1,(-3)^7}; top eigenvector has |<P>|^2 = 1/9 for all 63 P (Hoggar SIC)",
          np.allclose(w, [-3] * 7 + [21]) and np.allclose(flat, 1 / 9))

    # X5 orbit of the optimal violated set under Sp(6,2) (transvections): 120, stabiliser 12096
    L3, S3 = W5[1], W5[2]
    lid = {frozenset(lab[i] for i in l): k for k, l in enumerate(L3)}
    V0 = frozenset(k for k, (l, s) in enumerate(zip(L3, S3)) if x[l[0]] ^ x[l[1]] ^ x[l[2]] ^ s)
    gens = []
    for v in range(1, 64):
        t = {a: (a ^ v) if omega(a, v, 3) else a for a in range(1, 64)}
        gens.append([lid[frozenset(t[lab[i]] for i in l)] for l in L3])
    seen = {V0}; todo = [V0]
    while todo:
        Vs = todo.pop()
        for g in gens:
            W_ = frozenset(g[k] for k in Vs)
            if W_ not in seen: seen.add(W_); todo.append(W_)
    check("X5 Sp(6,2)-orbit of the optimal W(5,2) violated set has size 120 (stabiliser 1451520/120 = 12096)",
          len(seen) == 120 and 1451520 % 120 == 0 and 1451520 // 120 == 12096)

    # X6 Q+(7,2): spectral lower bound 315 = witness; equality structure
    N = 4; Xp = [a for a in range(1, 256) if is_sym(a, N)]; Lp = lines(Xp, N)
    lb = spectral_lower_ceiling(len(Lp), len(Xp), N)
    G = __import__("certify").geometry("Q+", 4)
    xq = [int(t) for t in open(os.path.join(HERE, "witness_Qp7_2.txt"))]
    v = __import__("certify").violations(xq, G[1], G[2])
    labq = [sum(int(p[i]) << i for i in range(4)) | sum(int(p[4 + i]) << (4 + i) for i in range(4)) for p in G[0]]
    M = sum((1 - 2 * xi) * pmat(a, 4) for a, xi in zip(labq, xq))
    w, V = np.linalg.eigh(M); psi = V[:, -1]
    ex = {a: abs(np.vdot(psi, pmat(a, 4) @ psi)) for a in range(1, 256)}
    check("X6 deg Q+(7,2) = 315: |X|=135, |L|=1575, spectral bound 315, witness violates 315; spectrum {45,(-3)^15};"
          " |<P>| = 1/3 on symmetric, 0 on antisymmetric",
          len(Xp) == 135 and len(Lp) == 1575 and lb == 315 and v == 315 and np.allclose(w, [-3] * 15 + [45])
          and all(abs(ex[a] - 1 / 3) < 1e-9 for a in Xp) and all(ex[a] < 1e-9 for a in range(1, 256) if not is_sym(a, N)))

    # X7 Haar constants: E|2B-1| = C(2m,m)/4^m (numerical integration), Wallis, and phi(c_N) >= 0.2679 for N >= 6
    ok = True
    for m in (1, 2, 4, 8):
        # E|2B-1| for B ~ Beta(m,m) by fine midpoint rule
        K = 200000; xs = (np.arange(K) + 0.5) / K
        dens = xs**(m - 1) * (1 - xs)**(m - 1) / (math.gamma(m)**2 / math.gamma(2 * m))
        ok &= abs(np.sum(np.abs(2 * xs - 1) * dens) / K - math.comb(2 * m, m) / 4**m) < 1e-6
    for N in range(2, 40):
        d = 2**N; m = d // 2
        wm = Fr(math.comb(2 * m, m), 4**m) if N <= 12 else None
        if wm is not None:   # Wallis: 1/(pi(m+1/2)) <= w^2 <= 1/(pi(m+1/4))
            ok &= float(wm)**2 * math.pi * (m + 0.5) >= 1 - 1e-12 and float(wm)**2 * math.pi * (m + 0.25) <= 1 + 1e-12
        c2 = 2 * (d - 1) / (math.pi * d)      # Wallis lower bound for c_N^2
        phi = c2**1.5 - (1 - c2)**1.5
        if N >= 6: ok &= phi * math.sqrt(1 - 4.0**-N) >= 0.2679
    ok &= 0.25 < 0.2679
    check("X7 Haar: E|<P>| = C(2m,m)/4^m (m=1,2,4,8); Wallis bounds; phi(c_N) sqrt(1-4^-N) >= 0.2679 for 6<=N<40;"
          " 2^-2 < 0.2679 (window 4)", ok)

    # X8 negative lines closed form and product witnesses (direct counts)
    def all_lines_W(N):
        out = []
        for a in range(1, 4**N):
            for b in range(a + 1, 4**N):
                c = a ^ b
                if c > b and omega(a, b, N) == 0: out.append((a, b, c, chi_int(a, b, N)))
        return out
    ok = True
    for N in (2, 3, 4, 5):
        LL = all_lines_W(N); neg = sum(1 for l in LL if l[3] < 0)
        ok &= len(LL) == L_W(N) and 24 * neg == 16**N + 4**N - 2 * 10**N
    check("X8a number of negative lines of W(2N-1,2) = (16^N + 4^N - 2*10^N)/24 (N=2..5: 3, 90, 1908, 35400)", ok)

    hogg = {0: 1}
    for a_, xi in zip(lab, x): hogg[a_] = 1 - 2 * xi
    def h_block(k, a):                         # block patterns: 1 -> all +1 ; 3 -> Hoggar
        return 1 if k == 1 else hogg[a]
    def tensor_val(comp, a, N):
        xs_, zs_ = a & ((1 << N) - 1), a >> N; off = 0; val = 1
        for k in comp:
            bx = (xs_ >> off) & ((1 << k) - 1); bz = (zs_ >> off) & ((1 << k) - 1)
            val *= h_block(k, bx | (bz << k)); off += k
        return val
    ok = True; det = []
    for N, comp, tau in ((4, (3, 1), 13240), (5, (3, 1, 1), 132400)):
        LL = all_lines_W(N)
        viol = sum(1 for a, b, c, s in LL if s * tensor_val(comp, a, N) * tensor_val(comp, b, N) * tensor_val(comp, c, N) < 0)
        pred = Fr(L_W(N), 2) - Fr(tau - 3 * 4**N + 2, 12)
        ok &= viol == pred; det.append(f"N={N}: {viol}")
    check("X8b tensor products (Hoggar x single-qubit) violate exactly |L|/2 - (prod tau - 3*4^N + 2)/12 (tau1=10, tau3=1324)",
          ok, ", ".join(det))

    # X9 strict chain rho_3 < ... < rho_11 (exact rationals; upper bounds from multiplicativity)
    tau = {1: 10, 3: 1324, 4: 13996, 5: 147052}
    best = {0: 1}
    for N in range(1, 13): best[N] = max(best[N - k] * tau[k] for k in tau if k <= N)
    ok = True
    for N in range(3, 11):
        up = Fr(L_W(N), 2) - Fr(best[N] - 3 * 4**N + 2, 12)
        lo = spectral_lower_ceiling(L_W(N + 1), 4**(N + 1) - 1, N + 1)
        ok &= up / L_W(N) < Fr(lo, L_W(N + 1))
    # block values tau_4, tau_5 from the certified witnesses U1, U5 of certify.py: tau = 12(|L|/2 - viol) + 3*4^N - 2
    ok &= 12 * (Fr(L_W(4), 2) - 1575) + 3 * 4**4 - 2 == 13996 and 12 * (Fr(L_W(5), 2) - 31479) + 3 * 4**5 - 2 == 147052
    ok &= 12 * (Fr(L_W(3), 2) - 63) + 3 * 4**3 - 2 == 1324
    check("X9 strict chain rho_3 < rho_4 < ... < rho_11 (upper: product witnesses; lower: ASY-3)", ok)

    # X10 window inequality exact form: dhi(N+4) <= 2^{-(N+4)/2} = 2^{-N/2}/4 (t(t+1) <= (t+2)^2 identity)
    ok = all((t * t - 1) * (t - 2)**2 * t <= (t * t - 4)**2 * (t - 1) for t in (2**N for N in range(2, 60)))
    check("X10 ASY-3 deficit bound <= 2^{-N/2}: (t^2-1)(t-2)^2 t <= (t^2-4)^2 (t-1) for t = 2^N, N=2..59", ok)


    # X11 ASY-5': measure-and-assign line correlation = kappa(2^{N-2}); kappa(1)=1/2, kappa(2)=23/64 (Monte Carlo, 5 sigma)
    ok = True; det = []
    nrng = np.random.default_rng(11)
    for N, kap, T in ((2, 0.5, 30000), (3, 23 / 64, 15000)):
        X = list(range(1, 4**N)); Pm = np.array([pmat(a, N) for a in X]); pos = {a: i for i, a in enumerate(X)}
        Ls = lines(X, N); ia = np.array([pos[l[0]] for l in Ls]); ib = np.array([pos[l[1]] for l in Ls]); ic = np.array([pos[l[2]] for l in Ls])
        ch = np.array([chi_int(l[0], l[1], N) for l in Ls])
        d = 2**N; vals = np.empty(T)
        for t in range(T):
            psi = nrng.normal(size=d) + 1j * nrng.normal(size=d); psi /= np.linalg.norm(psi)
            e = np.einsum('i,aij,j->a', psi.conj(), Pm, psi).real; g = np.where(e >= 0, 1, -1)
            vals[t] = np.mean(ch * g[ia] * g[ib] * g[ic])
        m, se = vals.mean(), vals.std() / np.sqrt(T)
        ok &= abs(m - kap) < 5 * se; det.append(f"N={N}: {m:.4f}+-{se:.4f} vs {kap:.4f}")
    G = nrng.gamma(2, size=(2000000, 4))
    A = G[:, 0] + G[:, 1] - G[:, 2] - G[:, 3]; B = G[:, 0] - G[:, 1] + G[:, 2] - G[:, 3]; Cc = G[:, 0] - G[:, 1] - G[:, 2] + G[:, 3]
    v = np.sign(A * B * Cc); ok &= abs(v.mean() - 23 / 64) < 5 * v.std() / np.sqrt(len(v))
    check("X11 measure-and-assign: E[chi g g g] per line = kappa(2^{N-2}) (N=2: 1/2, N=3: 23/64); Gamma-pairing form", ok, "; ".join(det))


    # ---------------------------------------------------------------- round 3 (blueprint/11)
    import json
    def stateexp(psi, N):
        return {a: float(np.vdot(psi, pmat(a, N) @ psi).real) for a in range(1, 4**N)}
    def count_viol(X, g, N):
        S = set(X); viol = 0; L = 0
        for a in X:
            for b in X:
                c = a ^ b
                if a < b < c and c in S and omega(a, b, N) == 0:
                    L += 1; viol += (chi_int(a, b, N) * g[a] * g[b] * g[c] < 0)
        return L, viol
    # X12 Q+(7,2): closed-form flat state psi = (|+>^4 - |0>^4) sqrt(2/3); sign pattern violates exactly 315
    N = 4; psi = np.full(16, 0.25) ; psi[0] -= 1; psi = psi / np.linalg.norm(psi)
    e = stateexp(psi.astype(complex), N)
    Xp = [a for a in range(1, 256) if is_sym(a, N)]
    flat = all(abs(abs(e[a]) - 1 / 3) < 1e-12 for a in Xp) and all(abs(e[a]) < 1e-12 for a in range(1, 256) if not is_sym(a, N))
    g = {a: (1 if e[a] > 0 else -1) for a in Xp}
    L, v = count_viol(Xp, g, N)
    check("X12 TIGHT: psi = (|+>^4 - |0>^4)sqrt(2/3) has |<P>| = 1/3 exactly on the 135 symmetric Paulis, 0 elsewhere;"
          " g = sign<P> violates 315 of 1575 lines of Q+(7,2)", flat and L == 1575 and v == 315)
    # X13 new exact degree: 5-qubit configuration X_496 (flat state, gamma = 1/4): deg = 480
    J = json.load(open(os.path.join(HERE, "flat5_496.json")))
    N = 5; X = J["X"]; g = {a: s_ for a, s_ in zip(X, J["g"])}
    psi = np.array(J["state_re"]) + 1j * np.array(J["state_im"])
    e = stateexp(psi, N)
    flat = all(abs(abs(e[a]) - 0.25) < 1e-4 for a in X) and all(abs(e[a]) < 1e-4 for a in range(1, 1024) if a not in g)
    L, v = count_viol(X, g, N)
    lb = spectral_lower_ceiling(L, len(X), N)
    check("X13 TIGHT: 5-qubit X_496 (n=496): |L| = 10880, exact spectral bound 480 = 5440 - 4960, witness violates 480 => deg = 480;"
          " state is flat (|<P>| = 1/4 on X, 0 off X)", len(X) == 496 and L == 10880 and lb == 480 and v == 480 and flat, f"L={L} lb={lb} v={v}")
    # X14 W(5,2): F2-kernel of incidence has dim 7 (64 linear + 64 quadratic gauges); 120 * 128 = 15360
    N = 3; LL = lines(list(range(1, 64)), N)
    M = np.zeros((len(LL), 63), dtype=np.uint8)
    for i, l in enumerate(LL):
        for a in l: M[i, a - 1] = 1
    r = 0; A = M.copy()
    for c in range(63):
        piv = [i for i in range(r, A.shape[0]) if A[i, c]]
        if not piv: continue
        A[[r, piv[0]]] = A[[piv[0], r]]
        for i in range(A.shape[0]):
            if i != r and A[i, c]: A[i] ^= A[r]
        r += 1
    q_in_kernel = all((pc(a & 7 & (a >> 3)) + pc(b & 7 & (b >> 3)) + pc(c & 7 & (c >> 3))) % 2 == 0 for a, b, c in LL)
    check("X14 W(5,2): incidence rank 56, kernel dim 7 (y(a) mod 2 is a non-linear kernel element); optimal assignments 120*128 = 15360",
          r == 56 and q_in_kernel and 120 * 128 == 15360)
    # X15 GAME-1: brute-force classical value of the line/point linear-system game = 1 - deg/(3|L|)
    def game_value(pts, LLs, signs):
        idx_ = {p: i for i, p in enumerate(pts)}; best = 0; bestdeg = len(LLs)
        for x in range(1 << len(pts)):
            win = 0; viol = 0
            for l, sg in zip(LLs, signs):
                xs = [(x >> idx_[p]) & 1 for p in l]
                # Alice: best satisfying triple (sum = sg) maximising agreement with Bob's bits
                agree = max(sum(int(t[j] == xs[j]) for j in range(3)) for t in itertools.product((0, 1), repeat=3) if sum(t) % 2 == sg)
                win += agree; viol += (sum(xs) % 2 != sg)
            best = max(best, win); bestdeg = min(bestdeg, viol)
        return Fr(best, 3 * len(LLs)), bestdeg
    N = 2; X2 = list(range(1, 16)); L2 = lines(X2, N); s2 = [0 if chi_int(a, b, N) == 1 else 1 for a, b, c in L2]
    val, dg = game_value(X2, L2, s2)
    ok = val == 1 - Fr(dg, 3 * len(L2)) and dg == 3 and val == Fr(14, 15)
    def lab2(st):
        return sum((st[i] in "XY") << i for i in range(2)) | sum((st[i] in "ZY") << (2 + i) for i in range(2))
    sq = [["XI", "IX", "XX"], ["IZ", "ZI", "ZZ"], ["XZ", "ZX", "YY"]]
    pm = [tuple(sorted(lab2(t) for t in r)) for r in sq] + [tuple(sorted(lab2(sq[i][j]) for i in range(3))) for j in range(3)]
    okpm = all(omega(a, b, 2) == 0 and a ^ b == c for a, b, c in [(l[0], l[1], l[2]) for l in pm])
    ptsm = sorted({p for l in pm for p in l}); spm = [0 if chi_int(l[0], l[1], 2) == 1 else 1 for l in pm]
    valm, dgm = game_value(ptsm, pm, spm)
    check("X15 GAME-1: brute-force classical value = 1 - deg/(3|L|): doily 14/15 (deg 3); Peres-Mermin square 17/18 (deg 1)",
          ok and okpm and dgm == 1 and valm == Fr(17, 18), f"doily {val}, PM {valm}")
    # X16 negative-line formula reproduces the published counts (Muller et al. 2024, Table 1): 1908, 35400, 615888
    check("X16 (16^N + 4^N - 2*10^N)/24 = 1908, 35400, 615888 for N = 4, 5, 6 (published negative-context counts)",
          [(16**N + 4**N - 2 * 10**N) // 24 for N in (4, 5, 6)] == [1908, 35400, 615888])
    # X17 NEG-1: explicit sign patterns cap what ASY-2 can prove: Q-(7,2) Lambda* >= 28.18 -> ceiling <= 297; W(7,2) -> <= 1488
    J = json.load(open(os.path.join(HERE, "qm7_L1_witness.json")))
    Mq = sum(gg * pmat(a, 4) for a, gg in zip(J["X"], J["g"]))
    lam = np.linalg.eigvalsh(Mq)[-1]
    def ceiling(Lc, n, d, lam_):
        F = d * n; return Lc / 2 - (lam_ * F - F * F / (d * lam_)) / (12 * d)
    W5x = __import__("certify").geometry("W", 4)
    xw = [int(t) for t in open(os.path.join(HERE, "witness_W7_2.txt"))]
    labw = [sum(int(p[i]) << i for i in range(4)) | sum(int(p[4 + i]) << (4 + i) for i in range(4)) for p in W5x[0]]
    lamw = np.linalg.eigvalsh(sum((1 - 2 * xi) * pmat(a, 4) for a, xi in zip(labw, xw)))[-1]
    cq, cw = ceiling(1071, 119, 16, lam), ceiling(5355, 255, 16, lamw)
    check("X17 NEG-1: lambda_max witnesses 28.183 (Q-(7,2)) and 21+16*sqrt(6) (W(7,2)) cap the ASY-2 method at <= 297 and <= 1488",
          len(J["X"]) == 119 and lam > 28.18 and abs(lamw - (21 + 16 * 6**0.5)) < 1e-9 and cq < 298 and cw < 1489,
          f"{cq:.2f}, {cw:.2f}")

    print(f"\n{sum(RES)}/{len(RES)} asymptotic checks passed")
    return all(RES)


if __name__ == "__main__":
    sys.path.insert(0, HERE)
    sys.exit(0 if main() else 1)

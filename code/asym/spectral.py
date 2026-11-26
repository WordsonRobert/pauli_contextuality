"""Spectral (trace) formula for the contextuality degree of induced Pauli configurations.

For a set X of non-identity N-qubit Pauli labels closed under 'commuting sums' (induced configuration: lines are all
commuting triples {a,b,a+b} inside X) and an assignment g: X -> {+1,-1}, put M_g = sum_{a in X} g(a) P(a).  Then
        sum_{lines l} chi(l) g(a)g(b)g(c) = tr(M_g^3) / (6 * 2^N)
so   violated(g) = |L|/2 - tr(M_g^3)/(12*2^N)   and   deg X = |L|/2 - max_g tr(M_g^3)/(12*2^N).
"""
import itertools, sys
import numpy as np
sys.path.insert(0, '..')

I2 = np.eye(2, dtype=complex); X = np.array([[0, 1], [1, 0]], complex)
Z = np.array([[1, 0], [0, -1]], complex); Y = 1j * X @ Z   # Y = iXZ, Hermitian


def pauli(v, N):
    """canonical P(x|z) = i^{x.z} X^x Z^z (tensor), v integer with bits: x_i = bit i, z_i = bit N+i"""
    M = np.array([[1]], complex)
    for i in range(N):
        x = (v >> i) & 1; z = (v >> (N + i)) & 1
        M = np.kron(M, [I2, X, Z, Y][x + 2 * z])
    return M


def omega(a, b, N):
    m = (1 << N) - 1
    return (bin((a & m) & (b >> N)).count('1') + bin((a >> N) & (b & m)).count('1')) & 1


def lines_of(Xset, N):
    S = set(Xset); L = []
    for a in Xset:
        for b in Xset:
            if a < b and omega(a, b, N) == 0 and (a ^ b) in S and (a ^ b) > b:
                L.append((a, b, a ^ b))
    return L


def line_sign(l, P):
    a, b, c = l
    prod = P[a] @ P[b] @ P[c]
    s = prod[0, 0].real
    assert abs(abs(s) - 1) < 1e-9 and np.allclose(prod, s * np.eye(len(prod)))
    return 1 if s > 0 else -1      # chi(l)


def check_identity(N, Xset, trials=5, seed=0):
    rng = np.random.default_rng(seed)
    P = {a: pauli(a, N) for a in Xset}
    L = lines_of(Xset, N)
    chi = {l: line_sign(l, P) for l in L}
    for _ in range(trials):
        g = {a: int(rng.choice([-1, 1])) for a in Xset}
        lhs = sum(chi[l] * g[l[0]] * g[l[1]] * g[l[2]] for l in L)
        M = sum(g[a] * P[a] for a in Xset)
        rhs = np.trace(M @ M @ M).real / (6 * 2 ** N)
        assert abs(lhs - rhs) < 1e-6, (lhs, rhs)
        viol = sum(1 for l in L if chi[l] * g[l[0]] * g[l[1]] * g[l[2]] < 0)
        assert abs(viol - (len(L) / 2 - np.trace(M @ M @ M).real / (12 * 2 ** N))) < 1e-6
    return len(L)


if __name__ == '__main__':
    for N in (2, 3, 4):
        full = list(range(1, 4 ** N))
        m = (1 << N) - 1
        qp = [a for a in full if bin((a & m) & (a >> N)).count('1') % 2 == 0]
        qm = [a for a in full if (bin((a & m) & (a >> N)).count('1') + (a & 1) + ((a >> N) & 1)) % 2 == 0]
        for name, S in (('W', full), ('Q+', qp), ('Q-', qm)):
            nl = check_identity(N, S, trials=3 if N == 4 else 6)
            print(f'N={N} {name}: points {len(S)} lines {nl}  identity OK')

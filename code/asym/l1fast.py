"""Fast alternating ascent for max_g lambda_max(M_g) / max L1 Pauli norm, any N (d = 2^N up to ~512).
Uses Walsh-Hadamard transforms; all 4^N Pauli expectations in O(4^N N). Writes the best sign pattern g
(as an assignment witness: bit = (1-g)/2, indexed by Pauli label (x,z) -> x + d*z) to witness_spec_N.txt."""
import numpy as np, sys

def fwht(a):  # along last axis, unnormalised
    a = a.copy(); h = 1; n = a.shape[-1]
    while h < n:
        a = a.reshape(a.shape[:-1] + (n // (2 * h), 2, h))
        x, y = a[..., 0, :].copy(), a[..., 1, :].copy()
        a[..., 0, :], a[..., 1, :] = x + y, x - y
        a = a.reshape(a.shape[:-3] + (n,)); h *= 2
    return a

def setup(N):
    d = 2**N; idx = np.arange(d)
    pc = np.array([bin(k).count('1') for k in range(d)])
    ph = (1j) ** pc[np.bitwise_and.outer(idx, idx)]          # ph[x,z] = i^{|x&z|}
    return d, idx, ph

def expectations(psi, d, idx, ph):
    # E[x,z] = i^{|x&z|} sum_j conj(psi[j^x]) (-1)^{z.j} psi[j]
    U = np.conj(psi[np.bitwise_xor.outer(idx, idx)]) * psi[None, :]   # U[x,j]
    return (ph * fwht(U)).real

def matrix(g, d, idx, ph):
    W = fwht(g * ph)                    # W[x,c] = sum_z g[x,z] i^{|x&z|} (-1)^{z.c}
    M = np.zeros((d, d), complex)
    for x in range(d): M[idx ^ x, idx] = W[x]
    return M

def run(N, trials, seed):
    d, idx, ph = setup(N); rng = np.random.default_rng(seed)
    nL = (4**N - 1) * (4**(N - 1) - 1) // 3
    best = (-1, None, None)
    for t in range(trials):
        psi = rng.normal(size=d) + 1j * rng.normal(size=d); psi /= np.linalg.norm(psi); val = -1
        for it in range(500):
            E = expectations(psi, d, idx, ph); g = np.where(E >= 0, 1.0, -1.0); g[0, 0] = 0.0
            M = matrix(g, d, idx, ph); w, V = np.linalg.eigh(M); psi = V[:, -1]
            if w[-1] <= val + 1e-10: break
            val = w[-1]
        tr3 = float(np.sum(w**3)); viol = nL / 2 - tr3 / (12 * d)
        if best[0] < 0 or viol < best[0] - 1e-6:
            best = (viol, g.copy(), w.copy())
            print(f'N={N} trial {t}: lambda_max {val:.4f} violations {viol:.2f}', flush=True)
    viol, g, w = best
    with open(f'witness_spec_{N}.txt', 'w') as f:
        for z in range(d):
            for x in range(d):
                if x or z: f.write(f'{x} {z} {int((1 - g[x, z]) // 2)}\n')
    vals, cnt = np.unique(np.round(w, 4), return_counts=True)
    print('spectrum', dict(zip(vals.tolist(), cnt.tolist())))
    return viol

if __name__ == '__main__':
    run(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))

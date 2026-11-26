"""ASY-6 certificate: tensor products of the single-qubit magic sign pattern (t: h(I)=1,h(X)=h(Y)=h(Z)=+1 after
gauge) and the optimal W(5,2) (Hoggar) pattern give explicit assignments of W(2N-1,2).  We COUNT their violations
directly (no spectral theory) and compare with the multiplicative prediction |L|/2 - (prod tau - 3*4^N + 2)/12.
Labels: integer a = x | (z << N), qubit i <-> bit i."""
import numpy as np, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'certificates'))
import certify as C

POP = np.array([bin(k).count('1') for k in range(1 << 16)], dtype=np.int64)
def pc(v): return POP[v & 0xFFFF] + POP[(v >> 16) & 0xFFFF]

def lines_and_signs(N):
    m = (1 << N) - 1; A = np.arange(1, 4**N, dtype=np.int64)
    out_a, out_b, out_s = [], [], []
    for a in range(1, 4**N):
        b = A[A > a]; c = a ^ b; keep = c > b; b = b[keep]; c = c[keep]
        xa, za, xb, zb = a & m, a >> N, b & m, b >> N
        om = (pc(xa & zb) + pc(za & xb)) & 1; b = b[om == 0]; c = c[om == 0]
        xb, zb, xc, zc = b & m, b >> N, c & m, c >> N
        k = (pc(xa & za) + pc(xb & zb) - pc(xc & zc) + 2 * pc(za & xb)) % 4
        assert np.all(k % 2 == 0)
        out_a.append(np.full(len(b), a)); out_b.append(b); out_s.append(1 - k)   # chi = +1 (k=0) or -1 (k=2)
    return np.concatenate(out_a), np.concatenate(out_b), np.concatenate(out_s)

def hoggar_h():
    """h on 3-qubit labels (incl. identity, h(0)=1) from certificates/witness_W5_2.txt"""
    pts, L, S = C.geometry('W', 3); x = [int(t) for t in open(os.path.join(os.path.dirname(C.__file__), 'witness_W5_2.txt'))]
    h = np.ones(64, dtype=np.int64)
    for p, xi in zip(pts, x):
        a = sum(int(p[i]) << i for i in range(3)) | sum(int(p[3 + i]) << (3 + i) for i in range(3))
        h[a] = 1 - 2 * xi
    return h

def single_h():
    return np.ones(4, dtype=np.int64)       # all-plus on I,X,Z,Y  (= sign pattern of a magic state, up to gauge)

def tensor_h(blocks):
    """h on N-qubit labels as product of block patterns; blocks = list of (n_i, h_i) in qubit order."""
    N = sum(n for n, _ in blocks); H = np.ones(4**N, dtype=np.int64); a = np.arange(4**N)
    x, z = a & ((1 << N) - 1), a >> N; off = 0
    for n, h in blocks:
        bx = (x >> off) & ((1 << n) - 1); bz = (z >> off) & ((1 << n) - 1)
        H *= h[bx | (bz << n)]; off += n
    return H

if __name__ == '__main__':
    tau = {1: 10, 3: 1324}
    for N, comp in [(2, [1, 1]), (3, [3]), (4, [3, 1]), (5, [3, 1, 1]), (6, [3, 3]), (7, [3, 3, 1])]:
        if N == 7 and '--big' not in sys.argv: continue
        blocks = [(n, hoggar_h() if n == 3 else single_h()) for n in comp]
        H = tensor_h(blocks)
        a, b, s = lines_and_signs(N)
        viol = int(np.sum(s * H[a] * H[b] * H[a ^ b] < 0)); nL = len(a)
        t = int(np.prod([tau[n] for n in comp]))
        pred = nL / 2 - (t - 3 * 4**N + 2) / 12
        print(f'N={N} blocks {comp}: lines {nL}, counted violations {viol}, predicted {pred}', flush=True)
        assert viol == pred

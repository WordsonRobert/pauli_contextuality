import numpy as np, sys, glob, itertools
from l1fast import setup, expectations
from product_witness import lines_and_signs
N = int(sys.argv[1]); fn = sys.argv[2]
d, idx, ph = setup(N); psi = np.load(fn)
E = expectations(psi.astype(complex), d, idx, ph)          # E[x,z]
lab = lambda x, z: x | (z << N)
e = np.zeros(4**N)
for x in range(d):
    for z in range(d): e[lab(x, z)] = E[x, z]
e = np.round(e * 1e6) / 1e6
X = [a for a in range(1, 4**N) if abs(e[a]) > 0.05]
vals = sorted(set(np.round(np.abs(e[X]), 4))); print('support', len(X), 'abs values', vals)
a, b, s = lines_and_signs(N)
inX = np.zeros(4**N, bool); inX[X] = True
keep = inX[a] & inX[b] & inX[a ^ b]
a, b, s = a[keep], b[keep], s[keep]; L = len(a)
g = np.sign(e).astype(int); g[g == 0] = 1
viol = int(np.sum(s * g[a] * g[b] * g[a ^ b] < 0))
n = len(X); gam = vals[0]
trM3 = (d - 1) * d * (d - 2) / gam**3
print('lines', L, 'violations of sign(e)', viol, ' predicted (L - trM3/(6d))/2 =', (L - trM3 / (6 * d)) / 2)
bound = L / 2 - n**1.5 * (d - 2) / (12 * np.sqrt(d - 1)); print('spectral lower bound', bound)
# structure: is X a quadric / complement of one?  test all quadratic forms q = x.z + c.(x,z)+ k-free: q(a) = popcount(x&z) + popcount(c & a)
pc = lambda v: bin(v).count('1')
m = (1 << N) - 1
for c in range(4**N):
    Q = [a_ for a_ in range(1, 4**N) if (pc(a_ & m & (a_ >> N)) + pc(c & a_)) % 2 == 0]
    if set(Q) == set(X): print('X = quadric zero set with c =', c); break
    Qc = [a_ for a_ in range(1, 4**N) if (pc(a_ & m & (a_ >> N)) + pc(c & a_)) % 2 == 1]
    if set(Qc) == set(X): print('X = nonsingular set of quadric with c =', c, '(hyperbolic' if pc(c & m & (c >> N)) % 2 == 0 else '(elliptic', ')'); break
else:
    print('X is not a quadric (or complement) of the standard family')
degs = np.bincount(np.concatenate([a, b, a ^ b]), minlength=4**N)[X]; print('lines per point', sorted(set(degs.tolist())))

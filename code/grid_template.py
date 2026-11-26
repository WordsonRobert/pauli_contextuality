"""Find 'odd grid path' templates: base line (a,b,c) = (ZI II, IZ II, ZZ II) on virtual qubits 1,2;
private qubits 3,4. Grid rows: [a,b,c], [p21,p22,p23], [p31,p32,p33]; columns {h_j, p2j, p3j}.
Need: rows 2,3 and columns are commuting triples summing to 0, all 9 points distinct, and the
6-line cycle has odd sign (so the 5 non-h lines act as an h-constraint with flipped sign)."""
import itertools, numpy as np
from engine import from_str, omega, product_sign, to_str
a, b = from_str("ZIII"), from_str("IZII"); c = (a ^ b)
h = [a, b, c]
allp = [np.array(v, dtype=np.uint8) for v in itertools.product([0, 1], repeat=8) if any(v)]
found = []
for p21 in allp:
    if omega(p21, a): continue
    for p22 in allp:
        if omega(p22, b) or omega(p21, p22): continue
        p23 = p21 ^ p22
        if not p23.any() or omega(p23, c): continue
        p2 = [p21, p22, p23]; p3 = [h[j] ^ p2[j] for j in range(3)]
        if any(not q.any() for q in p3): continue
        pts = h + p2 + p3
        if len({q.tobytes() for q in pts}) < 9: continue
        if any(omega(p3[i], p3[j]) for i, j in [(0, 1), (0, 2), (1, 2)]): continue
        if any(omega(h[j], p3[j]) or omega(p2[j], p3[j]) for j in range(3)): continue
        lines = [h, p2, p3] + [[h[j], p2[j], p3[j]] for j in range(3)]
        lam = sum(product_sign(l) for l in lines) % 2
        if lam:
            found.append(([to_str(q) for q in p2], [to_str(q) for q in p3]))
print("odd grid templates found:", len(found))
for f in found[:5]: print(f)
full = [f for f in found if all(s[2:] != "II" for s in f[0] + f[1])]
zonly = [f for f in full if all(ch in "IZ" for s in f[0]+f[1] for ch in s[2:])]
print("templates with every private part nonzero:", len(full), " of which private parts Z-only:", len(zonly))
for f in zonly[:4]: print(f)

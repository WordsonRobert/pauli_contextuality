"""Known configurations used as sanity checks."""
import itertools
import numpy as np
from engine import Config, from_str, omega


def magic_square():
    grid = [["XI", "IX", "XX"],
            ["IZ", "ZI", "ZZ"],
            ["XZ", "ZX", "YY"]]
    pts, idx = [], {}
    for r in grid:
        for s in r:
            idx[s] = len(pts)
            pts.append(from_str(s))
    rows = [tuple(idx[s] for s in r) for r in grid]
    cols = [tuple(idx[grid[i][j]] for i in range(3)) for j in range(3)]
    return Config(pts, rows + cols)


def pentagram():
    lines_s = [["XXX", "XYY", "YXY", "YYX"],
               ["XXX", "XII", "IXI", "IIX"],
               ["XYY", "XII", "IYI", "IIY"],
               ["YXY", "IXI", "YII", "IIY"],
               ["YYX", "IIX", "YII", "IYI"]]
    pts, idx = [], {}
    for l in lines_s:
        for s in l:
            if s not in idx:
                idx[s] = len(pts)
                pts.append(from_str(s))
    return Config(pts, [tuple(idx[s] for s in l) for l in lines_s])


def full_symplectic(N):
    """All lines {a, b, a+b} of W(2N-1, 2)."""
    pts = [np.array(b, dtype=np.uint8) for b in itertools.product([0, 1], repeat=2 * N) if any(b)]
    key = {p.tobytes(): i for i, p in enumerate(pts)}
    lines = set()
    for i, j in itertools.combinations(range(len(pts)), 2):
        if omega(pts[i], pts[j]) == 0:
            k = key[((pts[i] + pts[j]) % 2).astype(np.uint8).tobytes()]
            lines.add(tuple(sorted((i, j, k))))
    return Config(pts, sorted(lines))

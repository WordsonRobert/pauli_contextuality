"""Full geometries: W(2N-1,2), hyperbolic quadric Q+ (x.z = 0), elliptic quadric Q- (x.z + x1 + z1 = 0).
Exports instance files for the C local-search solver."""
import itertools, sys
import numpy as np
from engine import product_sign, omega


def all_points(N):
    return [np.array(b, dtype=np.uint8) for b in itertools.product([0, 1], repeat=2 * N) if any(b)]


def qform(kind, N):
    if kind == "W":
        return None
    if kind == "Q+":
        return lambda p: int(p[:N] @ p[N:]) % 2
    if kind == "Q-":
        return lambda p: (int(p[:N] @ p[N:]) + int(p[0]) + int(p[N])) % 2
    raise ValueError(kind)


def geometry(kind, N):
    q = qform(kind, N)
    pts = [p for p in all_points(N) if q is None or q(p) == 0]
    key = {p.tobytes(): i for i, p in enumerate(pts)}
    lines = set()
    for i, j in itertools.combinations(range(len(pts)), 2):
        if omega(pts[i], pts[j]) == 0:
            k = key.get(((pts[i] + pts[j]) % 2).astype(np.uint8).tobytes())
            if k is not None:
                lines.add(tuple(sorted((i, j, k))))
    lines = sorted(lines)
    signs = [product_sign([pts[a], pts[b], pts[c]]) for a, b, c in lines]
    return pts, lines, signs


def write_instance(path, npts, lines, signs):
    with open(path, "w") as f:
        f.write(f"{npts} {len(lines)}\n")
        for (a, b, c), s in zip(lines, signs):
            f.write(f"{a} {b} {c} {s}\n")


if __name__ == "__main__":
    kind, N = sys.argv[1], int(sys.argv[2])
    pts, lines, signs = geometry(kind, N)
    out = f"inst_{kind.replace('+','p').replace('-','m')}_{N}.txt"
    write_instance(out, len(pts), lines, signs)
    print(kind, N, "points", len(pts), "lines", len(lines), "negative", sum(signs), "L/5", len(lines) / 5, "->", out)

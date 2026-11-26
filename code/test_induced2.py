import numpy as np, sys, time
from induced_red import build, closure_lines
from engine import Config, degree, brute_min_unsat, min_unsat
rng = np.random.default_rng(42); fails = 0; t0 = time.time(); hist = {}
for trial in range(20):
    N, m = int(rng.integers(4, 8)), int(rng.integers(4, 10))
    H = np.zeros((m, N), np.uint8)
    for j in range(m): H[j, rng.choice(N, 3, replace=False)] = 1
    b = rng.integers(0, 2, m).astype(np.uint8)
    cfg = build(H, b)
    des = {tuple(sorted(c)) for c in cfg.contexts}; clo = closure_lines(cfg)
    if clo != des:
        fails += 1; print("closure mismatch", len(clo - des), len(des - clo)); continue
    want = brute_min_unsat(H, b) + int(b.sum())
    d, opt = degree(Config(cfg.points, sorted(clo)), time_limit=240)
    ok = d == want and opt; fails += not ok; hist[want - int(b.sum())] = hist.get(want - int(b.sum()), 0) + 1
    print(N, m, len(cfg.points), "deg", d, "want", want, "OK" if ok else "FAIL", flush=True)
print("20 instances: closure==designated and degree==OPT+f ; failures", fails, "OPT hist", dict(sorted(hist.items())), f"{time.time()-t0:.0f}s")

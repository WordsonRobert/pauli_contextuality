"""Arbitrary-length XOR systems -> compact line configurations inside the hyperbolic quadric."""
import numpy as np, time, math
from engine import degree, brute_min_unsat
from reduction import line_configuration_xor

rng = np.random.default_rng(11); fails = 0; t0 = time.time(); rows_out = []
for trial in range(14):
    N, m = int(rng.integers(4, 7)), int(rng.integers(4, 8))
    G = np.zeros((m, N), dtype=np.uint8)
    for j in range(m):
        G[j, rng.choice(N, int(rng.integers(1, min(N, 5) + 1)), replace=False)] = 1
    t = rng.integers(0, 2, m).astype(np.uint8)
    want = brute_min_unsat(G, t)
    cfg = line_configuration_xor(G, t, compact=True, seed=trial)
    P = np.stack(cfg.points); n = cfg.n_qubits
    on_quadric = bool(((P[:, :n].astype(int) * P[:, n:]).sum(1) % 2 == 0).all())
    lines_only = max(len(c) for c in cfg.contexts) == 3
    got, opt = degree(cfg)
    ok = want == got and opt and on_quadric and lines_only
    fails += not ok
    rows_out.append((N, m, int(G.sum()), want, got, len(cfg.points), len(cfg.contexts), n,
                     math.ceil(math.log(len(cfg.points) + 1, 4))))
    if not ok: print("FAIL", rows_out[-1], on_quadric, lines_only, opt)
print("N  m  |G|  min-unsat  degree  points  lines  qubits  (lower bound log4)")
for r in rows_out[:8]: print("%d  %2d  %3d  %5d  %6d  %6d  %5d  %4d  (%d)" % r)
print(f"14 random arbitrary-length systems: failures = {fails}  ({time.time()-t0:.0f}s)")

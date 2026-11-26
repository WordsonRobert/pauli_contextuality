"""Target B: are all optimal violated sets of Q-(7,2) equivalent under its collineation group?
Two violated sets are equivalent iff the coloured point-line incidence graphs are isomorphic (for Q-(7,2) every
incidence automorphism is induced by O^-(8,2), fundamental theorem of polar spaces)."""
import subprocess, sys, collections
from pynauty import Graph, certificate, autgrp
from geometry import geometry
pts, lines, signs = geometry("Q-", 4)
open("inst_Qm_4.txt", "w").write(f"{len(pts)} {len(lines)}\n" + "".join(f"{a} {b} {c} {s}\n" for (a, b, c), s in zip(lines, signs)))
def graph(V):
    n = len(pts) + len(lines)
    adj = {i: [] for i in range(n)}
    for j, l in enumerate(lines):
        for v in l: adj[len(pts) + j].append(v)
    viol = set(V)
    colors = [set(range(len(pts))), {len(pts) + j for j in range(len(lines)) if j in viol},
              {len(pts) + j for j in range(len(lines)) if j not in viol}]
    return Graph(n, directed=False, adjacency_dict=adj, vertex_coloring=colors)
g0 = Graph(len(pts) + len(lines), directed=False,
           adjacency_dict={len(pts) + j: list(l) for j, l in enumerate(lines)},
           vertex_coloring=[set(range(len(pts))), set(range(len(pts), len(pts) + len(lines)))])
print("|Aut(Q-(7,2) incidence)| =", int(autgrp(g0)[1]), flush=True)
certs = collections.Counter(); sizes = set(); found = set()
N = int(sys.argv[1]) if len(sys.argv) > 1 else 12
for s in range(N):
    subprocess.run(["./tabu", "inst_Qm_4.txt", "2", str(500 + s), f"/tmp/o{s}.txt"], capture_output=True)
    x = [int(t) for t in open(f"/tmp/o{s}.txt")]
    V = tuple(j for j, ((a, b, c), e) in enumerate(zip(lines, signs)) if x[a] ^ x[b] ^ x[c] ^ e)
    if len(V) != 315: print("run", s, "not optimal:", len(V)); continue
    found.add(V)
    G = graph(V); certs[certificate(G)] += 1; sizes.add(int(autgrp(G)[1]))
print(f"optimal violated sets found: {len(found)} distinct; isomorphism classes: {len(certs)}; |Stab(V)| values: {sizes}")
for st in sizes:
    print("orbit size |Aut|/|Stab| =", int(autgrp(g0)[1]) // st)

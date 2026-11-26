import numpy as np, subprocess, collections, sys
from geometry import geometry
from engine import omega
pts, lines, signs = geometry("Q-", 4)
P = np.stack(pts).astype(int); n=4
allv = [np.array(v) for v in np.ndindex(*(2,)*8) if any(v)]
q = lambda p: (int(p[:4]@p[4:]) + int(p[0]) + int(p[4])) % 2
def profile(x):
    V = [i for i,((a,b,c),s) in enumerate(zip(lines,signs)) if x[a]^x[b]^x[c]^s]
    Vs=set(V)
    par, tan = collections.Counter(), collections.Counter()
    for a in allv:
        a=np.array(a)
        inside=[i for i,l in enumerate(lines) if all(omega(a,pts[v])==0 for v in l)]
        k=sum(1 for i in inside if i in Vs)
        (tan if q(a)==0 else par)[k]+=1
    deg=collections.Counter(sum(1 for i in V if v in lines[i]) for v in range(len(pts)))
    return len(V), dict(sorted(par.items())), dict(sorted(tan.items())), dict(sorted(deg.items()))
for seed in range(int(sys.argv[1])):
    subprocess.run(["./tabu","inst_Qm_4.txt","3",str(100+seed),f"/tmp/opt{seed}.txt"],capture_output=True)
    x=[int(t) for t in open(f"/tmp/opt{seed}.txt")]
    v,par,tan,deg=profile(x)
    print(f"seed {seed}: |V|={v}\n  parabolic sections (63-min, 315 lines) violated-count histogram {par}\n  tangent sections (36-min, 207 lines) histogram {tan}\n  violated-lines-per-point histogram {deg}", flush=True)

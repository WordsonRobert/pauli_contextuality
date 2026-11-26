import numpy as np, itertools
from geometry import geometry
from engine import omega
pts, lines, signs = geometry("Q-", 4)
q = lambda p: (int(p[:4]@p[4:]) + int(p[0]) + int(p[4])) % 2
x=[int(t) for t in open("/tmp/opt0.txt")]
V=[i for i,((a,b,c),s) in enumerate(zip(lines,signs)) if x[a]^x[b]^x[c]^s]; Vs=set(V)
tight=[]
for v in itertools.product([0,1],repeat=8):
    a=np.array(v)
    if not a.any() or q(a)==0: continue
    k=sum(1 for i,l in enumerate(lines) if i in Vs and all(omega(a,pts[u])==0 for u in l))
    if k==63: tight.append(a)
print("tight parabolic sections:", [''.join(map(str,a)) for a in tight])
a1,a2,a3=tight
print("sum zero:", not ((a1+a2+a3)%2).any(), " omegas:", omega(a1,a2), omega(a1,a3), omega(a2,a3), " q:",q(a1),q(a2),q(a3))
inU=[omega(p,a1)==0 and omega(p,a2)==0 for p in pts]
deg={v:sum(1 for i in V if v in lines[i]) for v in range(len(pts))}
from collections import Counter
print("points in E^perp:", sum(inU), " their violated-degree histogram:", Counter(deg[v] for v in range(len(pts)) if inU[v]))
print("points outside E^perp histogram:", Counter(deg[v] for v in range(len(pts)) if not inU[v]))
Lin=[i for i,l in enumerate(lines) if all(inU[v] for v in l)]
print("lines inside E^perp:", len(Lin), " violated among them:", sum(1 for i in Lin if i in Vs))

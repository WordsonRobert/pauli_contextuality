"""Prove degree >= k+1 by showing 'at most k violated lines' is UNSAT (CryptoMiniSat, native XOR)."""
import sys, time, numpy as np
from pycryptosat import Solver
from engine import nullspace_f2
def load(fn):
    rows=[l.split() for l in open(fn).read().split("\n") if l]; n,m=map(int,rows[0])
    return n,m,[tuple(map(int,r)) for r in rows[1:]]
def at_most_k(s, lits, k, top):
    # sequential counter (Sinz). lits are positive ints. returns new top.
    n=len(lits)
    if k>=n: return top
    if k==0:
        for l in lits: s.add_clause([-l])
        return top
    R=[[0]*(k+1) for _ in range(n)]
    for i in range(n):
        for j in range(1,k+1): top+=1; R[i][j]=top
    for i in range(n):
        x=lits[i]
        s.add_clause([-x, R[i][1]])
        if i>0:
            for j in range(1,k+1):
                s.add_clause([-R[i-1][j], R[i][j]])
                if j>1: s.add_clause([-x, -R[i-1][j-1], R[i][j]])
            s.add_clause([-x, -R[i-1][k]])
    return top
def check(fn, k, threads=1):
    n,m,L=load(fn)
    H=np.zeros((m,n),np.uint8)
    for r,(a,b,c,_) in enumerate(L): H[r,[a,b,c]]=1
    K=nullspace_f2(H); Kr=K.copy(); piv=[]
    for i in range(len(Kr)):
        c=int(np.nonzero(Kr[i])[0][0]); piv.append(c)
        for j in range(len(Kr)):
            if j!=i and Kr[j,c]: Kr[j]^=Kr[i]
    s=Solver(threads=threads)
    X=lambda i:i+1; V=lambda r:n+r+1
    for c in piv: s.add_clause([-X(c)])
    for r,(a,b,c,e) in enumerate(L): s.add_xor_clause([X(a),X(b),X(c),V(r)], bool(e))
    at_most_k(s,[V(r) for r in range(m)],k,n+m)
    t=time.time(); sat,_=s.solve()
    return sat, time.time()-t
if __name__=="__main__":
    fn,k=sys.argv[1],int(sys.argv[2])
    sat,t=check(fn,k)
    print(fn, f"<= {k} violations:", "SAT" if sat else "UNSAT  => degree >= %d"%(k+1), f"({t:.1f}s)")

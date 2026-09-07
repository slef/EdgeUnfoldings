import numpy as np, collections, sys, time
from unfold import Polytope, unfold, overlaps
from gen import rand_points
from geodesic import shortest_vw
n=int(sys.argv[1]); rng=np.random.default_rng(int(sys.argv[2])); N=int(sys.argv[3])
res=collections.Counter(); cnt=0; t0=time.time(); both=[]
while cnt<N:
    P=rand_points(n,rng)
    try: p=Polytope(P)
    except: continue
    if len(p.P)!=n or len(p.faces)!=2*n-4: continue
    cnt+=1; key=tuple(sorted(p.deg.values()))
    adj=collections.defaultdict(set)
    for u,v in p.edges: adj[u].add(v); adj[v].add(u)
    hinge_index={(u,w):ei for ei,(f,g,u,w) in enumerate(p.E)}
    for v in range(n):
        far=[w for w in range(n) if w!=v and w not in adj[v]]
        if len(far)!=1: continue
        w=far[0]; L,seq,crossed=shortest_vw(p,v,w); last=crossed[-1]
        star={tuple(sorted((v,u))) for u in adj[v]}
        g={}
        for u in last:
            cut=star|{tuple(sorted((w,u)))}
            tree=[hinge_index[e] for e in p.edges if e not in cut]
            g[u]=overlaps(p.faces, unfold(p.faces,p.L,p.E,tree), p.eps)<=0
        res[(key,len(seq),sum(g.values()))]+=1
        if not any(g.values()): both.append((key,v,w,P.copy()))
print("samples",cnt,"time %.0f"%(time.time()-t0))
for k,c in sorted(res.items()): print("type",k[0],"faces on geodesic",k[1],"#good among the 2 crossed-edge endpoints =",k[2],":",c)
if both: np.save("bprime_fail_n%d.npy"%n,both[0][3]); print("B' FAILS:",both[0][:3])

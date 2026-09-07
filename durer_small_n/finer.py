import numpy as np, collections, sys, itertools, time
from unfold import Polytope
from gen import rand_points
n=int(sys.argv[1]); rng=np.random.default_rng(int(sys.argv[2])); N=int(sys.argv[3])
# For each polytope and each vertex v: consider cut trees = (all edges at v) + a spanning forest completion
# using only edges incident to non-neighbors of v ("star at v plus pendant edges").  Here we test
# the case where v's non-neighbors are pairwise nonadjacent (each gets one pendant edge).
res=collections.defaultdict(list); cnt=0; t0=time.time()
while cnt<N:
    P=rand_points(n,rng)
    try: p=Polytope(P)
    except: continue
    if len(p.P)!=n or len(p.faces)!=2*n-4: continue
    cnt+=1
    key=tuple(sorted(p.deg.values()))
    pen=p.penetrations(); good={t:(pe<=0) for t,pe in zip(p.trees(),pen)}
    adj=collections.defaultdict(set)
    for u,v in p.edges: adj[u].add(v); adj[v].add(u)
    for v in range(n):
        far=[w for w in range(n) if w!=v and w not in adj[v]]
        star={tuple(sorted((v,u))) for u in adj[v]}
        ok=0; tot=0
        for t in p.trees():
            cut=set(p.cut_set(t))
            if star<=cut and all(sum(1 for e in cut if w in e)==1 for w in far):
                tot+=1; ok+=good[t]
        res[(key,p.deg[v],len(far))].append((ok,tot))
print("samples",cnt,"time %.0f"%(time.time()-t0))
for k,v in sorted(res.items()):
    a=np.array(v); print("type",k[0],"deg(v)=",k[1],"#far=",k[2],"cases",len(a),"trees per case",a[0,1],
        "min good",a[:,0].min(),"never-good cases",int((a[:,0]==0).sum()))

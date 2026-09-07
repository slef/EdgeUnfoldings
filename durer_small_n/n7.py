import numpy as np, collections, sys, time
from unfold import Polytope
from gen import rand_points
n=int(sys.argv[1]); rng=np.random.default_rng(int(sys.argv[2])); N=int(sys.argv[3])
res=collections.defaultdict(lambda:[0,0,10**9]); mingood={}; cnt=0; t0=time.time(); ntrees={}
while cnt<N:
    P=rand_points(n,rng)
    try: p=Polytope(P)
    except: continue
    if len(p.P)!=n or len(p.faces)!=2*n-4: continue
    cnt+=1; key=tuple(sorted(p.deg.values()))
    pen=p.penetrations(); good={t:(pe<=0) for t,pe in zip(p.trees(),pen)}
    ng=sum(good.values()); ntrees[key]=len(good)
    mingood[key]=min(mingood.get(key,10**9),ng)
    adj=collections.defaultdict(set)
    for u,v in p.edges: adj[u].add(v); adj[v].add(u)
    for v in range(n):
        far=[w for w in range(n) if w!=v and w not in adj[v]]
        if len(far)>1: continue
        star={tuple(sorted((v,u))) for u in adj[v]}
        ok=0; tot=0
        for t in p.trees():
            cut=set(p.cut_set(t))
            if star<=cut: tot+=1; ok+=good[t]
        r=res[(key,p.deg[v])]; r[0]+=1; r[1]+=int(ok>0); r[2]=min(r[2],ok)
print("n=%d samples=%d time=%.0fs"%(n,cnt,time.time()-t0))
for k in sorted(mingood): print("type",k,"trees",ntrees[k],"min #good trees",mingood[k])
for k,(a,b,c) in sorted(res.items()):
    print("type",k[0],"star at deg-%d vertex (+pendant if needed): cases"%k[1],a,"some tree good",b,"min #good in family",c)

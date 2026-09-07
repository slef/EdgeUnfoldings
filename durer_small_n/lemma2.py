import numpy as np, collections, sys, time
from unfold import Polytope
from gen import rand_points
from geodesic import shortest_vw
n=int(sys.argv[1]); rng=np.random.default_rng(int(sys.argv[2])); N=int(sys.argv[3])
res=collections.defaultdict(lambda:[0,0,0]); cnt=0; t0=time.time(); worst=[]
while cnt<N:
    P=rand_points(n,rng)
    try: p=Polytope(P)
    except: continue
    if len(p.P)!=n or len(p.faces)!=2*n-4: continue
    cnt+=1; key=tuple(sorted(p.deg.values()))
    adj=collections.defaultdict(set)
    for u,v in p.edges: adj[u].add(v); adj[v].add(u)
    good=None
    for v in range(n):
        far=[w for w in range(n) if w!=v and w not in adj[v]]
        if len(far)!=1: continue
        w=far[0]
        if good is None:
            pen=p.penetrations(); good={t:(pe<=0) for t,pe in zip(p.trees(),pen)}
        L,seq,crossed=shortest_vw(p,v,w)
        last=crossed[-1]  # edge of link(w) crossed last
        star={tuple(sorted((v,u))) for u in adj[v]}
        for u in last:
            target=star|{tuple(sorted((w,u)))}
            for t in p.trees():
                if set(p.cut_set(t))==target:
                    r=res[(key,p.deg[v],len(seq))]; r[0]+=1; r[1]+=int(good[t])
                    if not good[t]: worst.append((key,v,w,u,P.copy()))
        res[(key,p.deg[v],len(seq))][2]+=1
print("samples",cnt,"time %.0f"%(time.time()-t0))
for k,(a,b,c) in sorted(res.items()):
    print("type",k[0],"deg(v)=",k[1],"faces on geodesic",k[2],": endpoint-pendant trees tested",a,"good",b,"(failures %d)"%(a-b))
if worst: np.save("lemma2_fail_n%d.npy"%n, worst[0][4]); print("first failure:",worst[0][:4])

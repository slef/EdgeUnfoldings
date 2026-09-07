import numpy as np, collections, sys, time
from unfold import Polytope, unfold
from gen import rand_points
from geodesic import shortest_vw
n=int(sys.argv[1]); rng=np.random.default_rng(int(sys.argv[2])); N=int(sys.argv[3])
rules=collections.defaultdict(lambda:[0,0]); cnt=0; t0=time.time()
def curv(p,v):
    tot=0
    for f in p.faces:
        if v in f:
            i=f.index(v); a=p.P[f[(i+1)%3]]-p.P[v]; b=p.P[f[(i+2)%3]]-p.P[v]
            tot+=np.arccos(np.clip(np.dot(a,b)/np.linalg.norm(a)/np.linalg.norm(b),-1,1))
    return 2*np.pi-tot
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
        star={tuple(sorted((v,u))) for u in adj[v]}
        g={}
        for u in adj[w]:
            target=star|{tuple(sorted((w,u)))}
            for t in p.trees():
                if set(p.cut_set(t))==target: g[u]=good[t]
        L,seq,crossed=shortest_vw(p,v,w); last=crossed[-1]
        # crossing point x on last edge: unfold faces seq
        feats={}
        for u in adj[w]:
            feats[u]=dict(edgepath=np.linalg.norm(p.P[v]-p.P[u])+np.linalg.norm(p.P[u]-p.P[w]),
                          dist_w=np.linalg.norm(p.P[u]-p.P[w]), dist_v=np.linalg.norm(p.P[u]-p.P[v]),
                          curv=curv(p,u), oncross=(u in last))
        cand={
         'min edgepath |vu|+|uw|': min(adj[w],key=lambda u:feats[u]['edgepath']),
         'max edgepath': max(adj[w],key=lambda u:feats[u]['edgepath']),
         'min |uw|': min(adj[w],key=lambda u:feats[u]['dist_w']),
         'max |uw|': max(adj[w],key=lambda u:feats[u]['dist_w']),
         'min |uv|': min(adj[w],key=lambda u:feats[u]['dist_v']),
         'max |uv|': max(adj[w],key=lambda u:feats[u]['dist_v']),
         'min curvature u': min(adj[w],key=lambda u:feats[u]['curv']),
         'max curvature u': max(adj[w],key=lambda u:feats[u]['curv']),
         'crossed edge, min |uw|': min(last,key=lambda u:feats[u]['dist_w']),
         'crossed edge, max |uw|': max(last,key=lambda u:feats[u]['dist_w']),
         'crossed edge, min edgepath': min(last,key=lambda u:feats[u]['edgepath']),
         'crossed edge, max edgepath': max(last,key=lambda u:feats[u]['edgepath']),
        }
        for name,u in cand.items():
            r=rules[(key,name)]; r[0]+=1; r[1]+=int(g[u])
        rules[(key,'ANY pendant good')][0]+=1; rules[(key,'ANY pendant good')][1]+=int(any(g.values()))
        rules[(key,'#good pendants (sum)')][0]+=len(g); rules[(key,'#good pendants (sum)')][1]+=sum(g.values())
print("samples",cnt,"time %.0f"%(time.time()-t0))
for k,(a,b) in sorted(rules.items()):
    print("type",k[0],"%-28s"%k[1],"cases",a,"good",b,"fail",a-b)

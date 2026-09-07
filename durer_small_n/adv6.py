import numpy as np, collections, sys, time
from unfold import Polytope, unfold, overlaps
from gen import rand_points
rng=np.random.default_rng(int(sys.argv[1])); budget=int(sys.argv[2])
def pendant_score(P):
    """min over vertices v of degree 4 (octahedron type): #good among the 4 star(v)+pendant trees; also max pen"""
    try: p=Polytope(P)
    except: return None
    if len(p.P)!=6 or len(p.faces)!=8 or tuple(sorted(p.deg.values()))!=(4,)*6: return None
    adj=collections.defaultdict(set)
    for u,w in p.edges: adj[u].add(w); adj[w].add(u)
    hinge_index={(u,w):ei for ei,(f,g,u,w) in enumerate(p.E)}
    best=(10,0.0)
    for v in range(6):
        w=[x for x in range(6) if x!=v and x not in adj[v]][0]
        star={tuple(sorted((v,u))) for u in adj[v]}
        goods=0; minpen=np.inf
        for u in adj[w]:
            cut=star|{tuple(sorted((w,u)))}
            tree=[hinge_index[e] for e in p.edges if e not in cut]
            pen=overlaps(p.faces, unfold(p.faces,p.L,p.E,tree), p.eps)
            goods+=int(pen<=0); minpen=min(minpen,pen)
        best=min(best,(goods,-minpen))
    return best
t0=time.time(); evals=0; worst=(10,0)
while evals<budget:
    P=rand_points(6,rng); s=pendant_score(P); evals+=1
    if s is None: continue
    cur=P; curs=s
    for it in range(60):
        Q=cur*np.exp(rng.normal(scale=0.15,size=cur.shape))+rng.normal(scale=0.02,size=cur.shape)*np.abs(cur).mean()
        sq=pendant_score(Q); evals+=1
        if sq is not None and sq<=curs: cur,curs=Q,sq
    if curs<worst: worst=curs; np.save("adv6_worst.npy",cur); print("new worst",worst,"after",evals,"evals, %.0fs"%(time.time()-t0),flush=True)
print("final worst (#good pendants at worst v, -min penetration):",worst,"evals",evals)

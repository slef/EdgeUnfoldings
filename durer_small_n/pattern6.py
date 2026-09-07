import numpy as np, collections, sys, time
from unfold import Polytope, unfold, overlaps
from gen import rand_points
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
pat=collections.Counter(); rule=collections.Counter(); cnt=0
while cnt<N:
    P=rand_points(6,rng)
    try: p=Polytope(P)
    except: continue
    if len(p.P)!=6 or len(p.faces)!=8 or tuple(sorted(p.deg.values()))!=(4,)*6: continue
    cnt+=1
    adj=collections.defaultdict(set)
    for u,w in p.edges: adj[u].add(w); adj[w].add(u)
    hinge_index={(u,w):ei for ei,(f,g,u,w) in enumerate(p.E)}
    for v in range(6):
        w=[x for x in range(6) if x!=v and x not in adj[v]][0]
        # cyclic order of equator around w
        ring=[]; start=next(iter(adj[w])); ring.append(start)
        while len(ring)<4:
            nxt=[x for x in adj[w] if x not in ring and x in adj[ring[-1]]][0]; ring.append(nxt)
        star={tuple(sorted((v,u))) for u in adj[v]}
        g=[]
        for u in ring:
            cut=star|{tuple(sorted((w,u)))}
            tree=[hinge_index[e] for e in p.edges if e not in cut]
            g.append(overlaps(p.faces, unfold(p.faces,p.L,p.E,tree), p.eps)<=0)
        # canonical pattern up to rotation/reflection of the 4-cycle
        best=None
        for r in range(4):
            for refl in (1,-1):
                s=tuple(g[(r+refl*i)%4] for i in range(4))
                if best is None or s>best: best=s
        pat[best]+=1
        # rule: longest edge at w
        lens=[np.linalg.norm(p.P[u]-p.P[w]) for u in ring]
        rule['longest |uw|']+=g[int(np.argmax(lens))]
        lens=[np.linalg.norm(p.P[u]-p.P[v]) for u in ring]
        rule['longest |uv|']+=g[int(np.argmax(lens))]
        # rule: the pendant u whose flap angle... : u maximizing angle at u in faces? try |uv|+|uw|
        lens=[np.linalg.norm(p.P[u]-p.P[v])+np.linalg.norm(p.P[u]-p.P[w]) for u in ring]
        rule['longest |uv|+|uw|']+=g[int(np.argmax(lens))]
        rule['cases']+=1
print("cases",rule['cases'])
for k,c in sorted(pat.items(),key=lambda kv:-kv[1]): print(" good-pattern around w (cyclic):",k,c)
for k,c in rule.items(): print(k,c)

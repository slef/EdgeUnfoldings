import numpy as np, collections, sys, itertools
from unfold import Polytope
from gen import rand_points
from geostar import place, cross
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
def ang(p,F,x):
    i=F.index(x); a=p.P[F[(i+1)%3]]-p.P[x]; b=p.P[F[(i+2)%3]]-p.P[x]
    return np.arccos(np.clip(np.dot(a,b)/np.linalg.norm(a)/np.linalg.norm(b),-1,1))
st=collections.Counter(); cnt=0; ex=None
while cnt<N:
    P=rand_points(6,rng)
    try: p=Polytope(P)
    except: continue
    if len(p.P)!=6 or len(p.faces)!=8 or tuple(sorted(p.deg.values()))!=(4,)*6: continue
    cnt+=1
    adj=collections.defaultdict(set)
    for a,b in p.edges: adj[a].add(b); adj[b].add(a)
    fidx={frozenset(f):i for i,f in enumerate(p.faces)}
    curv={x:2*np.pi-sum(ang(p,F,x) for F in p.faces if x in F) for x in range(6)}
    pairs=set()
    for v in range(6):
        w=[x for x in range(6) if x!=v and x not in adj[v]][0]; pairs.add(tuple(sorted((v,w))))
    nconv={}; nreflex_total=0
    for (v,w) in pairs:
        ring=[next(iter(adj[w]))]
        while len(ring)<4: ring.append([x for x in adj[w] if x not in ring and x in adj[ring[-1]]][0])
        c=0
        for i in range(4):
            u1,u2=ring[i],ring[(i+1)%4]; fV=fidx[frozenset((v,u1,u2))]; fW=fidx[frozenset((w,u1,u2))]
            e=ang(p,p.faces[fV],u1)+ang(p,p.faces[fW],u1); f=ang(p,p.faces[fV],u2)+ang(p,p.faces[fW],u2)
            c+=(e<np.pi and f<np.pi)
        nconv[(v,w)]=c
    best=max(nconv.values()); st['max #convex quads over the 3 pairs = %d'%best]+=1
    # pair containing the sharpest vertex
    vs=max(range(6),key=lambda x:curv[x]); pr=[q for q in pairs if vs in q][0]
    st['pair with sharpest vertex: #convex = %d'%nconv[pr]]+=1
    if best<4 and ex is None: ex=(P.copy(),nconv)
print("octahedra",cnt)
for k,c in sorted(st.items()): print(k,c)

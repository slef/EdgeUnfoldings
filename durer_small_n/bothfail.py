import numpy as np, collections, sys, itertools
from unfold import Polytope, unfold
from unfold2 import sat_pen
from gen import rand_points
from geostar import place, cross, rot
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2]); shown=0
def curv(p,x):
    tot=0
    for F in p.faces:
        if x in F:
            i=F.index(x); a=p.P[F[(i+1)%3]]-p.P[x]; b=p.P[F[(i+2)%3]]-p.P[x]
            tot+=np.arccos(np.clip(np.dot(a,b)/np.linalg.norm(a)/np.linalg.norm(b),-1,1))
    return 2*np.pi-tot
def ang(p,F,x):  # angle of face F at vertex x
    i=F.index(x); a=p.P[F[(i+1)%3]]-p.P[x]; b=p.P[F[(i+2)%3]]-p.P[x]
    return np.arccos(np.clip(np.dot(a,b)/np.linalg.norm(a)/np.linalg.norm(b),-1,1))
cnt=0; agg=collections.Counter()
while cnt<N and shown<6:
    P=rand_points(6,rng)
    try: p=Polytope(P)
    except: continue
    if len(p.P)!=6 or len(p.faces)!=8 or tuple(sorted(p.deg.values()))!=(4,)*6: continue
    cnt+=1
    adj=collections.defaultdict(set)
    for a,b in p.edges: adj[a].add(b); adj[b].add(a)
    fidx={frozenset(f):i for i,f in enumerate(p.faces)}; hinge_index={(a,b):ei for ei,(f,g,a,b) in enumerate(p.E)}
    for v in range(6):
        w=[x for x in range(6) if x!=v and x not in adj[v]][0]
        ring=[next(iter(adj[w]))]
        while len(ring)<4: ring.append([x for x in adj[w] if x not in ring and x in adj[ring[-1]]][0])
        star={tuple(sorted((v,u))) for u in adj[v]}
        conv=[];diag=[];goodZ=[];badpairs=[]
        for i in range(4):
            u1,u2=ring[i],ring[(i+1)%4]; fV=fidx[frozenset((v,u1,u2))]; fW=fidx[frozenset((w,u1,u2))]
            pos=place(p,[fW,fV]); W=pos[fW]; V=pos[fV]
            c=cross(V[v],W[w],W[u1])*cross(V[v],W[w],W[u2])<0 and cross(W[u1],W[u2],V[v])*cross(W[u1],W[u2],W[w])<0
            conv.append(c); diag.append(np.linalg.norm(V[v]-W[w]) if c else np.inf)
            cut=star|{tuple(sorted((w,u1)))}; tree=[hinge_index[e] for e in p.edges if e not in cut]
            posZ=unfold(p.faces,p.L,p.E,tree); bad=[]
            for f,g in itertools.combinations(range(8),2):
                sh=set(p.faces[f])&set(p.faces[g])
                if any(np.linalg.norm(posZ[f][x]-posZ[g][x])<p.eps for x in sh): continue
                if sat_pen(np.array([posZ[f][x] for x in p.faces[f]]),np.array([posZ[g][x] for x in p.faces[g]]))>p.eps:
                    nm=lambda F:('V' if v in p.faces[F] else 'W')+''.join(str(ring.index(x)+1) for x in p.faces[F] if x not in (v,w))
                    bad.append(nm(f)+'-'+nm(g))
            goodZ.append(not bad); badpairs.append(bad)
        j=int(np.argmin(diag))
        if not goodZ[j] and not goodZ[(j+1)%4]:
            shown+=1
            print("=== both-fail case; shortest edge j=%d (u%d u%d); convex edges %s; good Z %s"%(j+1,j+1,(j+1)%4+1,[i+1 for i in range(4) if conv[i]],[i+1 for i in range(4) if goodZ[i]]))
            print("  overlaps:",{i+1:badpairs[i] for i in range(4) if badpairs[i]})
            print("  kappa: v %.3f w %.3f "%(curv(p,v),curv(p,w))+" ".join("u%d %.3f"%(i+1,curv(p,ring[i])) for i in range(4)))
            print("  fan angles at w:"," ".join("%.3f"%ang(p,p.faces[fidx[frozenset((w,ring[i],ring[(i+1)%4]))]],w) for i in range(4)),
                  " | flap angles at v:"," ".join("%.3f"%ang(p,p.faces[fidx[frozenset((v,ring[i],ring[(i+1)%4]))]],v) for i in range(4)))
            print("  |w u_i|:"," ".join("%.2f"%np.linalg.norm(p.P[w]-p.P[ring[i]]) for i in range(4))," |v u_i|:"," ".join("%.2f"%np.linalg.norm(p.P[v]-p.P[ring[i]]) for i in range(4)),
                  " |u_i u_i+1|:"," ".join("%.2f"%np.linalg.norm(p.P[ring[i]]-p.P[ring[(i+1)%4]]) for i in range(4)))

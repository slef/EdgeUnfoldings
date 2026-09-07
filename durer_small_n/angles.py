import numpy as np, collections, sys, itertools
from unfold import Polytope, unfold
from unfold2 import sat_pen
from gen import rand_points
from geostar import place, cross
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
def ang(p,F,x):
    i=F.index(x); a=p.P[F[(i+1)%3]]-p.P[x]; b=p.P[F[(i+2)%3]]-p.P[x]
    return np.arccos(np.clip(np.dot(a,b)/np.linalg.norm(a)/np.linalg.norm(b),-1,1))
st=collections.Counter(); cnt=0
while cnt<N:
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
        kw=2*np.pi-sum(ang(p,p.faces[fidx[frozenset((w,ring[i],ring[(i+1)%4]))]],w) for i in range(4))
        star={tuple(sorted((v,u))) for u in adj[v]}
        # e[i]: angle of Q_i at u_i ; f[i]: angle of Q_{i-1} at u_i
        e=[];f=[];conv=[];diag=[];good=[]
        for i in range(4):
            u1,u2=ring[i],ring[(i+1)%4]; fV=fidx[frozenset((v,u1,u2))]; fW=fidx[frozenset((w,u1,u2))]
            e.append(ang(p,p.faces[fV],u1)+ang(p,p.faces[fW],u1)); f.append(ang(p,p.faces[fV],u2)+ang(p,p.faces[fW],u2))  # f here is angle of Q_i at u_{i+1}
            pos=place(p,[fW,fV]); W=pos[fW]; V=pos[fV]
            c=cross(V[v],W[w],W[u1])*cross(V[v],W[w],W[u2])<0 and cross(W[u1],W[u2],V[v])*cross(W[u1],W[u2],W[w])<0
            conv.append(c); diag.append(np.linalg.norm(V[v]-W[w]) if c else np.inf)
            cut=star|{tuple(sorted((w,u1)))}; tree=[hinge_index[q] for q in p.edges if q not in cut]
            posZ=unfold(p.faces,p.L,p.E,tree); bad=False
            for a,b in itertools.combinations(range(8),2):
                sh=set(p.faces[a])&set(p.faces[b])
                if any(np.linalg.norm(posZ[a][x]-posZ[b][x])<p.eps for x in sh): continue
                if sat_pen(np.array([posZ[a][x] for x in p.faces[a]]),np.array([posZ[b][x] for x in p.faces[b]]))>p.eps: bad=True; break
            good.append(not bad)
        # f_i in my notation (angle of Q_{i-1} at u_i) = f[(i-1)%4] here
        F=[f[(i-1)%4] for i in range(4)]
        j=int(np.argmin(diag))
        both=not good[j] and not good[(j+1)%4]
        # conditions at the shortest edge j: Q_{j-1} reflex at u_j : F[j] > pi ; Q_{j+1} reflex at u_{j+1}: e[(j+1)%4] > pi
        cond=(F[j]>np.pi+kw) and (e[(j+1)%4]>np.pi+kw)
        cond_pi=(F[j]>np.pi) and (e[(j+1)%4]>np.pi)
        st['cases']+=1
        if both:
            st['both-fail']+=1
            st['both-fail & F_j>pi+k & e_j+1>pi+k']+=cond
            st['both-fail & F_j>pi & e_j+1>pi']+=cond_pi
            st['both-fail & Q_j+2 convex']+=conv[(j+2)%4]
        if cond_pi:
            st['adjacent reflex (>pi) cases']+=1; st['adjacent reflex & Q_j+2 convex']+=conv[(j+2)%4]
            st['adjacent reflex & Z_j+2 and Z_j+3 both good']+=(good[(j+2)%4] and good[(j+3)%4])
        if cond:
            st['adjacent reflex (>pi+k) cases']+=1; st['adjacent reflex (>pi+k) & Q_j+2 convex']+=conv[(j+2)%4]
for k,c in sorted(st.items()): print(k,c)

import numpy as np, collections, sys, itertools
from unfold import Polytope
from gen import rand_points
from geostar import place
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
def ang(p,F,x):
    i=F.index(x); a=p.P[F[(i+1)%3]]-p.P[x]; b=p.P[F[(i+2)%3]]-p.P[x]
    return np.arccos(np.clip(np.dot(a,b)/np.linalg.norm(a)/np.linalg.norm(b),-1,1))
def angle3(a,b,c):
    x=a-b; y=c-b; return np.arccos(np.clip(np.dot(x,y)/np.linalg.norm(x)/np.linalg.norm(y),-1,1))
st=collections.Counter(); cnt=0; viol=[]
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
    for v in range(6):
        w=[x for x in range(6) if x!=v and x not in adj[v]][0]
        ring=[next(iter(adj[w]))]
        while len(ring)<4: ring.append([x for x in adj[w] if x not in ring and x in adj[ring[-1]]][0])
        hyp = all(curv[v]>=curv[u] for u in ring)
        om=[];Fw=[];Bw=[];a=[];ap=[];b=[];bp=[]
        for i in range(4):
            u1,u2=ring[i],ring[(i+1)%4]; fV=fidx[frozenset((v,u1,u2))]; fW=fidx[frozenset((w,u1,u2))]
            om.append(ang(p,p.faces[fW],w))
            a.append(ang(p,p.faces[fV],u1)); ap.append(ang(p,p.faces[fV],u2))   # V_i angle at u_i, at u_{i+1}
            b.append(ang(p,p.faces[fW],u1)); bp.append(ang(p,p.faces[fW],u2))   # W_i angle at u_i, at u_{i+1}
            e=a[-1]+b[-1]; f=ap[-1]+bp[-1]
            pos=place(p,[fW,fV]); W=pos[fW]; V=pos[fV]
            Fw.append(angle3(W[u2],W[w],V[v]) if f>np.pi else 0.0)  # forward lean over ray w u_{i+1}
            Bw.append(angle3(V[v],W[w],W[u1]) if e>np.pi else 0.0)  # backward lean over ray w u_i
        for i in range(4):
            j=(i+1)%4; jj=(i+2)%4; k=curv[ring[j]]
            full=Fw[i]>=om[j]  # lean over whole arc of W_{i+1}
            st['cases']+=1
            if full:
                st['full forward lean']+=1
                if hyp: st['full forward lean under hyp kv>=eq']+=1; viol.append((curv[v],[curv[u] for u in ring]))
                # necessary condition check: a_{i+1}+kappa_{i+1} < om_{i+1}+b_{i+1}
                if not (a[j]+k < om[j]+b[j]-1e-9): st['full lean but nec. cond. violated (BUG?)']+=1
            fullB=Bw[i]>=om[(i-1)%4]
            if fullB:
                st['full backward lean']+=1
                if hyp: st['full backward lean under hyp']+=1
print("octahedra",cnt)
for k_,c in sorted(st.items()): print("  %-44s %d"%(k_,c))
for x in viol[:5]: print("  violation example kv=%.3f ring=%s"%(x[0],np.round(x[1],3)))

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
st=collections.Counter(); cnt=0; rows=[]
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
    v=max(range(6),key=lambda x:curv[x]); w=[x for x in range(6) if x!=v and x not in adj[v]][0]
    ring=[next(iter(adj[w]))]
    while len(ring)<4: ring.append([x for x in adj[w] if x not in ring and x in adj[ring[-1]]][0])
    kw=curv[w]; k=max(range(4),key=lambda i:curv[ring[i]]); uk=ring[k]
    if curv[uk]+kw>=np.pi: continue
    # angles at u_k: e_k (Q_k side: V_k, W_k), f_k (Q_{k-1} side)
    u_next=ring[(k+1)%4]; u_prev=ring[(k-1)%4]
    fVk=fidx[frozenset((v,uk,u_next))]; fWk=fidx[frozenset((w,uk,u_next))]
    fVp=fidx[frozenset((v,u_prev,uk))]; fWp=fidx[frozenset((w,u_prev,uk))]
    a=ang(p,p.faces[fVk],uk); b=ang(p,p.faces[fWk],uk); ap=ang(p,p.faces[fVp],uk); bp=ang(p,p.faces[fWp],uk)
    e=a+b; f=ap+bp
    # actual lean over ray k
    lean=0.0
    if f>np.pi:
        pos=place(p,[fWp,fVp]); W=pos[fWp]; V=pos[fVp]; lean=angle3(W[uk],W[w],V[v])
    if e>np.pi:
        pos=place(p,[fWk,fVk]); W=pos[fWk]; V=pos[fVk]; lean=angle3(V[v],W[w],W[uk])
    rows.append((curv[uk],kw,curv[v],e,f,lean,a,b,ap,bp,ang(p,p.faces[fVk],v),ang(p,p.faces[fVp],v)))
rows=np.array(rows)
print("octahedra",cnt,"cases with kappa_u+kappa_w<pi:",len(rows))
print("max lean/kw ratio %.3f"%(rows[:,5]/rows[:,1]).max(), " max lean %.3f"%rows[:,5].max())
print("max of max(e,f)-pi : %.3f ; max of (max(e,f)-pi)-kw: %.3f"%((np.maximum(rows[:,3],rows[:,4])-np.pi).max(), (np.maximum(rows[:,3],rows[:,4])-np.pi-rows[:,1]).max()))
print("cases with reflex at u_k (max(e,f)>pi):",int((np.maximum(rows[:,3],rows[:,4])>np.pi).sum()))
print("min kappa_v %.3f, min kappa_u %.3f, max kappa_w %.3f"%(rows[:,2].min(),rows[:,0].min(),rows[:,1].max()))
# W angles at u_k
print("max b, bp (W angles at u_k): %.3f %.3f ; max a, ap (V angles at u_k): %.3f %.3f"%(rows[:,7].max(),rows[:,9].max(),rows[:,6].max(),rows[:,8].max()))

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
st=collections.Counter(); cnt=0; fails=[]
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
    kw=curv[w]; om=[];Fw=[];Bw=[];e=[];f=[]
    for i in range(4):
        u1,u2=ring[i],ring[(i+1)%4]; fV=fidx[frozenset((v,u1,u2))]; fW=fidx[frozenset((w,u1,u2))]
        om.append(ang(p,p.faces[fW],w))
        e.append(ang(p,p.faces[fV],u1)+ang(p,p.faces[fW],u1)); f.append(ang(p,p.faces[fV],u2)+ang(p,p.faces[fW],u2))
        pos=place(p,[fW,fV]); W=pos[fW]; V=pos[fV]
        psi1=angle3(W[u1],W[w],V[v]); psi2=angle3(V[v],W[w],W[u2])
        Fw.append(max(0.0,psi1-om[-1]) if f[-1]>np.pi else 0.0); Bw.append(max(0.0,psi2-om[-1]) if e[-1]>np.pi else 0.0)
    k=max(range(4),key=lambda i:curv[ring[i]])  # pendant = sharpest neighbor of w
    i=lambda t:(k+t)%4
    c=[Bw[i(0)]+Fw[i(3)]<kw, Fw[i(0)]+Bw[i(3)]<om[i(1)]+om[i(2)], Fw[i(0)]+Bw[i(2)]<om[i(1)],
       Bw[i(0)]+Fw[i(2)]<om[i(3)]+kw, Fw[i(1)]+Bw[i(3)]<om[i(2)], Bw[i(1)]+Fw[i(3)]<kw+om[i(0)]]
    st['cases']+=1; st['all six hold']+=all(c)
    for j,cc in enumerate(c):
        if not cc: st['ineq %d fails'%(j+1)]+=1
    # also record whether kappa_k + kappa_w >= pi
    st['k_u+k_w>=pi']+= (curv[ring[k]]+kw>=np.pi)
    if not all(c) and len(fails)<8:
        fails.append(dict(kv=round(curv[v],3),kw=round(kw,3),ku=[round(curv[ring[i(t)]],3) for t in range(4)],om=[round(om[i(t)],3) for t in range(4)],
                          F=[round(Fw[i(t)],3) for t in range(4)],B=[round(Bw[i(t)],3) for t in range(4)],failed=[j+1 for j,cc in enumerate(c) if not cc]))
for k_,c_ in sorted(st.items()): print(k_,c_)
for d in fails: print(d)

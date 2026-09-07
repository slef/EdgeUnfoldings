import numpy as np, collections, sys, itertools
from unfold import Polytope
from gen import rand_points
from geostar import place
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
def ang(p,F,x):
    i=F.index(x); a=p.P[F[(i+1)%3]]-p.P[x]; b=p.P[F[(i+2)%3]]-p.P[x]
    return np.arccos(np.clip(np.dot(a,b)/np.linalg.norm(a)/np.linalg.norm(b),-1,1))
st=collections.Counter(); cnt=0; worst_examples=[]
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
        kw=curv[w]; om=[];Fw=[];Bw=[]
        for i in range(4):
            u1,u2=ring[i],ring[(i+1)%4]; fV=fidx[frozenset((v,u1,u2))]; fW=fidx[frozenset((w,u1,u2))]
            om.append(ang(p,p.faces[fW],w))
            e=ang(p,p.faces[fV],u1)+ang(p,p.faces[fW],u1); f=ang(p,p.faces[fV],u2)+ang(p,p.faces[fW],u2)
            pos=place(p,[fW,fV]); W=pos[fW]; V=pos[fV]
            psi=ang(p,[w,u1,v] if False else None,None) if False else None
            # angle u1 w v  and angle v w u2 in the development
            def angle3(a,b,c):  # angle at b
                x=a-b; y=c-b; return np.arccos(np.clip(np.dot(x,y)/np.linalg.norm(x)/np.linalg.norm(y),-1,1))
            psi1=angle3(W[u1],W[w],V[v]); psi2=angle3(V[v],W[w],W[u2])
            F=max(0.0,psi1-om[-1]) if f>np.pi else 0.0   # reflex at u2 -> forward lean
            B=max(0.0,psi2-om[-1]) if e>np.pi else 0.0   # reflex at u1 -> backward lean
            Fw.append(F); Bw.append(B)
        ok_k=[]
        for k in range(4):
            i=lambda t:(k+t)%4
            c=[Fw[i(0)]+Bw[i(2)]<om[i(1)], Bw[i(0)]+Fw[i(2)]<om[i(3)]+kw, Fw[i(1)]+Bw[i(3)]<om[i(2)],
               Bw[i(1)]+Fw[i(3)]<kw+om[i(0)], Bw[i(0)]+Fw[i(3)]<kw, Fw[i(0)]+Bw[i(3)]<om[i(1)]+om[i(2)]]
            ok_k.append(all(c))
        st['cases']+=1; st['some k passes wedge test']+=any(ok_k)
        if v==max(range(6),key=lambda x:curv[x]): st['v=spike cases']+=1; st['v=spike: some k passes']+=any(ok_k)
        if not any(ok_k) and len(worst_examples)<3: worst_examples.append((v,w,P.copy(),om,Fw,Bw,kw))
for k,c in sorted(st.items()): print(k,c)
for v,w,P,om,Fw,Bw,kw in worst_examples:
    print("example: kw=%.3f om=%s F=%s B=%s"%(kw,np.round(om,3),np.round(Fw,3),np.round(Bw,3)))

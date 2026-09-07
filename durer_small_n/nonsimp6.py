import numpy as np, collections, sys, time
from unfold2 import Polytope
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
def rand_prism_diag():
    # bottom triangle A,B,C ; top C' free; B' in plane(B,C,C'); A' in plane(A,C,C')  -> quads BCC'B', CAA'C' planar, ABB'A' not
    while True:
        A,B,C=rng.normal(size=(3,3)); Cp=rng.normal(size=3)+np.array([0,0,3])*np.exp(rng.uniform(-2,2))
        s,t=rng.uniform(0.2,2,size=2); Bp=C+s*(B-C)+t*(Cp-C)
        s,t=rng.uniform(0.2,2,size=2); Ap=C+s*(A-C)+t*(Cp-C)
        P=np.array([A,B,C,Ap,Bp,Cp])*np.exp(rng.uniform(-2,2,size=3))
        return P
def rand_octa_minus_edge():
    # octahedron-like: v,w and u1..u4, with v,u1,u2,u3 coplanar (quad u1 u2 u3 ... containing v) 
    while True:
        P=rng.normal(size=(6,3))*np.exp(rng.uniform(-2,2,size=3))
        v,u1,u2,u3=P[0],P[2],P[3],P[4]
        # force coplanarity of v,u1,u2,u3 by projecting u2 onto plane(v,u1,u3)
        n=np.cross(u1-v,u3-v); n/=np.linalg.norm(n); P[3]=u2-np.dot(u2-v,n)*n
        return P
stats=collections.defaultdict(lambda:[0,0,0,10**9]); cnt=collections.Counter(); t0=time.time()
for gen in (rand_prism_diag, rand_octa_minus_edge):
  tries=0
  while cnt[gen.__name__]<N and tries<20*N:
    tries+=1; P=gen()
    try: p=Polytope(P)
    except: continue
    fs=tuple(sorted(len(f) for f in p.faces)); key=(gen.__name__,fs,tuple(sorted(p.deg.values())))
    if len(p.P)!=6: continue
    if gen.__name__=='rand_prism_diag' and fs!=(3,3,3,3,4,4): continue
    if gen.__name__=='rand_octa_minus_edge' and fs!=(3,3,3,3,3,3,4): continue
    cnt[gen.__name__]+=1
    pen=p.penetrations(); good={t:(pe<=0) for t,pe in zip(p.trees(),pen)}
    adj=collections.defaultdict(set)
    for u,w in p.edges: adj[u].add(w); adj[w].add(u)
    S=stats[key]; S[0]+=1; S[3]=min(S[3],sum(good.values())); S[2]=len(good)
    fam_ok=False
    for v in range(6):
        far=[w for w in range(6) if w!=v and w not in adj[v]]
        if len(far)>1: continue
        star={tuple(sorted((v,u))) for u in adj[v]}
        if any(good[t] for t in p.trees() if star<=set(p.cut_set(t))): fam_ok=True
        else: print("  FAMILY FAILS for v=",v,key); np.save("fail_%s.npy"%gen.__name__,P)
    S[1]+=int(fam_ok)
print("time %.0f"%(time.time()-t0))
for k,(a,b,c,d) in stats.items(): print(k,"samples",a,"trees",c,"min #good",d,"star+pendant family (max-degree vertex) has a net in",b,"of",a)

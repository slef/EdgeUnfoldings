import numpy as np, collections, sys, itertools
from unfold import Polytope, unfold
from unfold2 import sat_pen
from gen import rand_points
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
def ang(p,F,x):
    i=F.index(x); a=p.P[F[(i+1)%3]]-p.P[x]; b=p.P[F[(i+2)%3]]-p.P[x]
    return np.arccos(np.clip(np.dot(a,b)/np.linalg.norm(a)/np.linalg.norm(b),-1,1))
st=collections.Counter(); cnt=0; ex=[]
while cnt<N:
    P=rand_points(6,rng)
    try: p=Polytope(P)
    except: continue
    if len(p.P)!=6 or len(p.faces)!=8 or tuple(sorted(p.deg.values()))!=(4,)*6: continue
    cnt+=1
    adj=collections.defaultdict(set)
    for a,b in p.edges: adj[a].add(b); adj[b].add(a)
    fidx={frozenset(f):i for i,f in enumerate(p.faces)}; hinge_index={(a,b):ei for ei,(f,g,a,b) in enumerate(p.E)}
    curv={x:2*np.pi-sum(ang(p,F,x) for F in p.faces if x in F) for x in range(6)}
    for v in range(6):
        w=[x for x in range(6) if x!=v and x not in adj[v]][0]
        ring=[next(iter(adj[w]))]
        while len(ring)<4: ring.append([x for x in adj[w] if x not in ring and x in adj[ring[-1]]][0])
        star={tuple(sorted((v,u))) for u in adj[v]}
        kv,kw=curv[v],curv[w]; keq=max(curv[u] for u in ring)
        for k in range(4):
            r=ring[k:]+ring[:k]
            cut=star|{tuple(sorted((w,r[0])))}; tree=[hinge_index[q] for q in p.edges if q not in cut]
            pos=unfold(p.faces,p.L,p.E,tree)
            Wf=[fidx[frozenset((w,r[i],r[(i+1)%4]))] for i in range(4)]; Vf=[fidx[frozenset((v,r[i],r[(i+1)%4]))] for i in range(4)]
            def ov(a,b):
                sh=set(p.faces[a])&set(p.faces[b])
                if any(np.linalg.norm(pos[a][x]-pos[b][x])<p.eps for x in sh): return False
                return sat_pen(np.array([pos[a][x] for x in p.faces[a]]),np.array([pos[b][x] for x in p.faces[b]]))>p.eps
            farpairs={'V1-W3':(Vf[0],Wf[2]),'V3-W1':(Vf[2],Wf[0]),'V2-W4':(Vf[1],Wf[3]),'V4-W2':(Vf[3],Wf[1]),'V1-V3':(Vf[0],Vf[2]),'V2-V4':(Vf[1],Vf[3])}
            hit=[nm for nm,(a,b) in farpairs.items() if ov(a,b)]
            for cond,name in ((kv>=kw,'kv>=kw'),(kv>=keq,'kv>=max equator'),(kv>=kw and kv>=keq,'v sharpest'),(kv<kw,'kv<kw'),(kv>=kw and kv<keq,'kv>=kw but < some equator')):
                if cond:
                    st[name+' cases']+=1
                    if hit: st[name+' FAR overlap']+=1
            if hit and kv>=kw:
                ex.append((round(kv,3),round(kw,3),[round(curv[u],3) for u in r],hit))
print("octahedra",cnt)
for k,c in sorted(st.items()): print("  %-34s %d"%(k,c))
for e in ex[:10]: print("  example (kv,kw,kappa ring from slit, pairs):",e)

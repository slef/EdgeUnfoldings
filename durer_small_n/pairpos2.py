import numpy as np, collections, sys, itertools
from unfold import Polytope, unfold
from unfold2 import sat_pen
from gen import rand_points
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
    curv={x:2*np.pi-sum(ang(p,F,x) for F in p.faces if x in F) for x in range(6)}
    order=sorted(range(6),key=lambda x:-curv[x])
    for rank,v in enumerate(order):
        w=[x for x in range(6) if x!=v and x not in adj[v]][0]
        ring=[next(iter(adj[w]))]
        while len(ring)<4: ring.append([x for x in adj[w] if x not in ring and x in adj[ring[-1]]][0])
        star={tuple(sorted((v,u))) for u in adj[v]}
        for k in range(4):
            r=ring[k:]+ring[:k]
            cut=star|{tuple(sorted((w,r[0])))}; tree=[hinge_index[q] for q in p.edges if q not in cut]
            pos=unfold(p.faces,p.L,p.E,tree)
            Wf=[fidx[frozenset((w,r[i],r[(i+1)%4]))] for i in range(4)]
            Vf=[fidx[frozenset((v,r[i],r[(i+1)%4]))] for i in range(4)]
            def ov(a,b):
                sh=set(p.faces[a])&set(p.faces[b])
                if any(np.linalg.norm(pos[a][x]-pos[b][x])<p.eps for x in sh): return False
                return sat_pen(np.array([pos[a][x] for x in p.faces[a]]),np.array([pos[b][x] for x in p.faces[b]]))>p.eps
            far=[(Vf[0],Wf[2]),(Vf[2],Wf[0]),(Vf[1],Wf[3]),(Vf[3],Wf[1]),(Vf[0],Vf[2]),(Vf[1],Vf[3])]
            loc=[(Vf[0],Vf[3]),(Vf[0],Wf[3]),(Vf[3],Wf[0])]
            key='v rank %d (0=sharpest)'%rank
            st[key+' cases']+=1
            st[key+' far overlap']+=any(ov(a,b) for a,b in far)
            st[key+' local overlap']+=any(ov(a,b) for a,b in loc)
            # also: w sharpest? i.e. rank of w
            wr=order.index(w)
            if wr==0:
                st['w sharpest: cases']+=1; st['w sharpest: far overlap']+=any(ov(a,b) for a,b in far); st['w sharpest: local overlap']+=any(ov(a,b) for a,b in loc)
print("octahedra",cnt)
for k,c in sorted(st.items()): print("  %-36s %d"%(k,c))

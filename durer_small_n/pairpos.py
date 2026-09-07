import numpy as np, collections, sys, itertools
from unfold import Polytope, unfold
from unfold2 import sat_pen
from gen import rand_points
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
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
        star={tuple(sorted((v,u))) for u in adj[v]}
        for k in range(4):
            r=ring[k:]+ring[:k]  # r[0]=u_k (slit), fan order W(r0 r1), W(r1 r2), W(r2 r3), W(r3 r0)
            cut=star|{tuple(sorted((w,r[0])))}; tree=[hinge_index[q] for q in p.edges if q not in cut]
            pos=unfold(p.faces,p.L,p.E,tree)
            Wf=[fidx[frozenset((w,r[i],r[(i+1)%4]))] for i in range(4)]
            Vf=[fidx[frozenset((v,r[i],r[(i+1)%4]))] for i in range(4)]
            def ov(a,b):
                sh=set(p.faces[a])&set(p.faces[b])
                if any(np.linalg.norm(pos[a][x]-pos[b][x])<p.eps for x in sh): return False
                return sat_pen(np.array([pos[a][x] for x in p.faces[a]]),np.array([pos[b][x] for x in p.faces[b]]))>p.eps
            st['cases']+=1
            names={('V1','W3'):(Vf[0],Wf[2]),('V3','W1'):(Vf[2],Wf[0]),('V2','W4'):(Vf[1],Wf[3]),('V4','W2'):(Vf[3],Wf[1]),
                   ('V1','V3'):(Vf[0],Vf[2]),('V2','V4'):(Vf[1],Vf[3]),('V1','V4'):(Vf[0],Vf[3]),('V1','W4'):(Vf[0],Wf[3]),('V4','W1'):(Vf[3],Wf[0])}
            for nm,(a,b) in names.items():
                if ov(a,b): st['overlap %s-%s'%nm]+=1
print("pendant unfoldings tested",st['cases'])
print("(fan order W1..W4 starting at the slit; V_i is the petal on W_i; V4,W4 are the pieces across the gap)")
for k,c in sorted(st.items()):
    if k!='cases': print("  %-16s %d"%(k,c))

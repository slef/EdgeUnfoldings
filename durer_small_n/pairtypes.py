import numpy as np, collections, sys, itertools
from unfold import Polytope, unfold
from unfold2 import sat_pen
from gen import rand_points
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
types=collections.Counter(); combos=collections.Counter(); cnt=0; nfail=0
while cnt<N:
    P=rand_points(6,rng)
    try: p=Polytope(P)
    except: continue
    if len(p.P)!=6 or len(p.faces)!=8 or tuple(sorted(p.deg.values()))!=(4,)*6: continue
    cnt+=1
    adj=collections.defaultdict(set)
    for a,b in p.edges: adj[a].add(b); adj[b].add(a)
    hinge_index={(a,b):ei for ei,(f,g,a,b) in enumerate(p.E)}
    for v in range(6):
        w=[x for x in range(6) if x!=v and x not in adj[v]][0]
        ring=[next(iter(adj[w]))]
        while len(ring)<4: ring.append([x for x in adj[w] if x not in ring and x in adj[ring[-1]]][0])
        star={tuple(sorted((v,u))) for u in adj[v]}
        for k in range(4):
            u=ring[k]  # pendant w-u ; relabel ring so that u=ring[0]
            r=ring[k:]+ring[:k]  # r[0]=u1, r[1]=u2, r[2]=u3, r[3]=u4
            idx={x:i+1 for i,x in enumerate(r)}
            cut=star|{tuple(sorted((w,u)))}; tree=[hinge_index[e] for e in p.edges if e not in cut]
            pos=unfold(p.faces,p.L,p.E,tree); bad=set()
            for f,g in itertools.combinations(range(8),2):
                sh=set(p.faces[f])&set(p.faces[g])
                if any(np.linalg.norm(pos[f][x]-pos[g][x])<p.eps for x in sh): continue
                pen=sat_pen(np.array([pos[f][x] for x in p.faces[f]]),np.array([pos[g][x] for x in p.faces[g]]))
                if pen>p.eps:
                    def nm(f):
                        F=p.faces[f]; eq=sorted(idx[x] for x in F if x not in (v,w))
                        return ('V' if v in F else 'W')+''.join(map(str,eq))
                    a,b=sorted((nm(f),nm(g)))
                    # classify
                    if {a,b}=={'V12','V14'}: t='flank V12-V41'
                    elif {a,b} in ({'V12','W14'},{'V14','W12'}): t='flap vs fan across gap'
                    elif {a,b} in ({'V12','V34'},{'V23','V14'}): t='opposite flaps'
                    elif {a,b} in ({'V12','W34'},{'V34','W12'},{'V23','W14'},{'V14','W23'}): t='flap vs opposite fan face'
                    else: t='other '+a+'-'+b
                    bad.add(t)
            if bad:
                nfail+=1
                for t in bad: types[t]+=1
                combos[tuple(sorted(bad))]+=1
print("octahedra",cnt,"failing pendant unfoldings",nfail)
for t,c in types.most_common(): print("  %-32s %d"%(t,c))
print("combinations:")
for t,c in combos.most_common(): print("  ",c,t)

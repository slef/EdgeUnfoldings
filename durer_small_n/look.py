import numpy as np, collections, sys, itertools
from unfold import Polytope, unfold
P=np.load(sys.argv[1]); v=int(sys.argv[2]); w=int(sys.argv[3])
p=Polytope(P)
adj=collections.defaultdict(set)
for a,b in p.edges: adj[a].add(b); adj[b].add(a)
hinge_index={(a,b):ei for ei,(f,g,a,b) in enumerate(p.E)}
def curv(x):
    tot=0
    for f in p.faces:
        if x in f:
            i=f.index(x); a=p.P[f[(i+1)%3]]-p.P[x]; b=p.P[f[(i+2)%3]]-p.P[x]
            tot+=np.arccos(np.clip(np.dot(a,b)/np.linalg.norm(a)/np.linalg.norm(b),-1,1))
    return 2*np.pi-tot
print("faces",p.faces); print("curvatures",{x:round(curv(x),3) for x in range(len(P))})
# ring around w
ring=[next(iter(adj[w]))]
while len(ring)<len(adj[w]): ring.append([x for x in adj[w] if x not in ring and x in adj[ring[-1]]][0])
print("v",v,"w",w,"ring",ring, "edge lengths |wu|",[round(np.linalg.norm(P[u]-P[w]),3) for u in ring],"|vu|",[round(np.linalg.norm(P[u]-P[v]),3) for u in ring])
star={tuple(sorted((v,u))) for u in adj[v]}
def name(f): 
    f=p.faces[f]; return ('V' if v in f else 'W' if w in f else '?')+''.join(str(x) for x in f if x not in (v,w))
for u in ring:
    cut=star|{tuple(sorted((w,u)))}; tree=[hinge_index[e] for e in p.edges if e not in cut]
    pos=unfold(p.faces,p.L,p.E,tree); bad=[]
    for f,g in itertools.combinations(range(len(p.faces)),2):
        sh=set(p.faces[f])&set(p.faces[g])
        if any(np.linalg.norm(pos[f][x]-pos[g][x])<p.eps for x in sh): continue
        from unfold2 import sat_pen
        pen=sat_pen(np.array([pos[f][x] for x in p.faces[f]]),np.array([pos[g][x] for x in p.faces[g]]))
        if pen>p.eps: bad.append((name(f),name(g),round(pen/p.scale,4)))
    print(" pendant w-%d:"%u, "NET" if not bad else "overlaps "+str(bad))

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
    hinge_index={(a,b):ei for ei,(f,g,a,b) in enumerate(p.E)}
    curv={x:2*np.pi-sum(ang(p,F,x) for F in p.faces if x in F) for x in range(6)}
    def simple(v,u):
        w=[x for x in range(6) if x!=v and x not in adj[v]][0]
        cut={tuple(sorted((v,y))) for y in adj[v]}|{tuple(sorted((w,u)))}
        tree=[hinge_index[q] for q in p.edges if q not in cut]; pos=unfold(p.faces,p.L,p.E,tree)
        for a,b in itertools.combinations(range(8),2):
            sh=set(p.faces[a])&set(p.faces[b])
            if any(np.linalg.norm(pos[a][x]-pos[b][x])<p.eps for x in sh): continue
            if sat_pen(np.array([pos[a][x] for x in p.faces[a]]),np.array([pos[b][x] for x in p.faces[b]]))>p.eps: return False
        return True
    dist=lambda a,b: np.linalg.norm(p.P[a]-p.P[b])
    vmax=max(range(6),key=lambda x:curv[x]); wmax=[x for x in range(6) if x!=vmax and x not in adj[vmax]][0]
    vmin=min(range(6),key=lambda x:curv[x]); wmin=[x for x in range(6) if x!=vmin and x not in adj[vmin]][0]
    st['cases']+=1
    st['v=maxcurv: some pendant']+=any(simple(vmax,u) for u in adj[wmax])
    st['v=maxcurv, u=argmax |vu|']+=simple(vmax,max(adj[wmax],key=lambda u:dist(vmax,u)))
    st['v=maxcurv, u=argmax |wu|']+=simple(vmax,max(adj[wmax],key=lambda u:dist(wmax,u)))
    st['v=maxcurv, u=argmax curv']+=simple(vmax,max(adj[wmax],key=lambda u:curv[u]))
    st['v=maxcurv, u=argmin curv']+=simple(vmax,min(adj[wmax],key=lambda u:curv[u]))
    st['v=maxcurv, u=argmax |vu|+|uw|']+=simple(vmax,max(adj[wmax],key=lambda u:dist(vmax,u)+dist(wmax,u)))
    st['v=maxcurv, u=argmin |vu|+|uw|']+=simple(vmax,min(adj[wmax],key=lambda u:dist(vmax,u)+dist(wmax,u)))
    st['v=maxcurv, u=argmax |vu|-|uw|']+=simple(vmax,max(adj[wmax],key=lambda u:dist(vmax,u)-dist(wmax,u)))
    st['v=mincurv: some pendant']+=any(simple(vmin,u) for u in adj[wmin])
    st['v=mincurv, u=argmax |vu|']+=simple(vmin,max(adj[wmin],key=lambda u:dist(vmin,u)))
    # w = max curvature (star at the antipode of the spike), pendant at the spike
    st['w=maxcurv: some pendant']+=any(simple(wmax,u) for u in adj[vmax])
    st['w=maxcurv, u=argmax |wu| (farthest from spike)']+=simple(wmax,max(adj[vmax],key=lambda u:dist(vmax,u)))
    st['w=maxcurv, u=argmin |wu| (closest to spike)']+=simple(wmax,min(adj[vmax],key=lambda u:dist(vmax,u)))
    st['w=maxcurv, u=argmax |vu| (far from star center)']+=simple(wmax,max(adj[vmax],key=lambda u:dist(wmax,u)))
    st['w=maxcurv, u=argmax curv']+=simple(wmax,max(adj[vmax],key=lambda u:curv[u]))
    st['w=maxcurv, u=argmax |vu|+|uw|']+=simple(wmax,max(adj[vmax],key=lambda u:dist(vmax,u)+dist(wmax,u)))
print("octahedra",cnt)
for k,c in sorted(st.items()): print("%-48s %d  fail %d"%(k,c,st['cases']-c))

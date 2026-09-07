import numpy as np, collections, sys, itertools, time
from unfold import Polytope, unfold
from unfold2 import sat_pen
from gen import rand_points
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2]); mode=sys.argv[3] if len(sys.argv)>3 else 'sample'
def ang(p,F,x):
    i=F.index(x); a=p.P[F[(i+1)%3]]-p.P[x]; b=p.P[F[(i+2)%3]]-p.P[x]
    return np.arccos(np.clip(np.dot(a,b)/np.linalg.norm(a)/np.linalg.norm(b),-1,1))
def pen_of(p,v,u,adj,hinge_index):
    w=[x for x in range(6) if x!=v and x not in adj[v]][0]
    cut={tuple(sorted((v,y))) for y in adj[v]}|{tuple(sorted((w,u)))}
    tree=[hinge_index[q] for q in p.edges if q not in cut]; pos=unfold(p.faces,p.L,p.E,tree); worst=0
    for a,b in itertools.combinations(range(8),2):
        sh=set(p.faces[a])&set(p.faces[b])
        if any(np.linalg.norm(pos[a][x]-pos[b][x])<p.eps for x in sh): continue
        worst=max(worst,sat_pen(np.array([pos[a][x] for x in p.faces[a]]),np.array([pos[b][x] for x in p.faces[b]])))
    return worst/p.scale
RULES=['u=argmax curv','u=argmax |vu|','u=argmax |wu|','u=argmax |vu|+|uw|','w=spike,u=closest to spike']
def evaluate(P):
    try: p=Polytope(P)
    except: return None
    if len(p.P)!=6 or len(p.faces)!=8 or tuple(sorted(p.deg.values()))!=(4,)*6: return None
    adj=collections.defaultdict(set)
    for a,b in p.edges: adj[a].add(b); adj[b].add(a)
    hinge_index={(a,b):ei for ei,(f,g,a,b) in enumerate(p.E)}
    curv={x:2*np.pi-sum(ang(p,F,x) for F in p.faces if x in F) for x in range(6)}
    dist=lambda a,b: np.linalg.norm(p.P[a]-p.P[b])
    v=max(range(6),key=lambda x:curv[x]); w=[x for x in range(6) if x!=v and x not in adj[v]][0]
    out={}
    out['u=argmax curv']=pen_of(p,v,max(adj[w],key=lambda u:curv[u]),adj,hinge_index)
    out['u=argmax |vu|']=pen_of(p,v,max(adj[w],key=lambda u:dist(v,u)),adj,hinge_index)
    out['u=argmax |wu|']=pen_of(p,v,max(adj[w],key=lambda u:dist(w,u)),adj,hinge_index)
    out['u=argmax |vu|+|uw|']=pen_of(p,v,max(adj[w],key=lambda u:dist(v,u)+dist(w,u)),adj,hinge_index)
    out['w=spike,u=closest to spike']=pen_of(p,w,min(adj[v],key=lambda u:dist(v,u)),adj,hinge_index)
    return out
t0=time.time()
if mode=='sample':
    st=collections.Counter(); cnt=0
    while cnt<N:
        r=evaluate(rand_points(6,rng))
        if r is None: continue
        cnt+=1
        for k,val in r.items(): st[k]+=int(val>1e-9)
    print("octahedra",cnt,"time %.0f"%(time.time()-t0))
    for k in RULES: print("%-32s failures %d"%(k,st[k]))
else:
    # adversarial hill climb on each rule: maximize penetration
    for rule in RULES:
        best=(0,None); evals=0
        while evals<N:
            P=rand_points(6,rng); r=evaluate(P); evals+=1
            if r is None: continue
            cur,curs=P,r[rule]
            for it in range(80):
                Q=cur*np.exp(rng.normal(scale=0.12,size=cur.shape))+rng.normal(scale=0.02,size=cur.shape)*np.abs(cur).mean()
                rq=evaluate(Q); evals+=1
                if rq is not None and rq[rule]>=curs: cur,curs=Q,rq[rule]
            if curs>best[0]: best=(curs,cur.copy())
        print("%-32s max penetration found %.2e"%(rule,best[0]))
        if best[0]>1e-9: np.save("adv_"+rule.replace(' ','_').replace('|','').replace('=','').replace(',','_')+".npy",best[1])

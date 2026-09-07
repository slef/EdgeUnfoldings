import numpy as np, collections, sys, time
from unfold import Polytope
from gen import rand_points
n=int(sys.argv[1]); rng=np.random.default_rng(int(sys.argv[2])); N=int(sys.argv[3])
res=collections.defaultdict(lambda:[0,0,10**9,10**9]); cnt=0; t0=time.time(); fails=[]
while cnt<N:
    P=rand_points(n,rng)
    try: p=Polytope(P)
    except: continue
    if len(p.P)!=n or len(p.faces)!=2*n-4: continue
    cnt+=1; key=tuple(sorted(p.deg.values()))
    pen=p.penetrations(); good=[pe<=0 for pe in pen]
    cuts=[set(p.cut_set(t)) for t in p.trees()]
    adj=collections.defaultdict(set)
    for u,v in p.edges: adj[u].add(v); adj[v].add(u)
    for v in range(n):
        star={tuple(sorted((v,u))) for u in adj[v]}
        fam=[g for c,g in zip(cuts,good) if star<=c]
        r=res[(key,p.deg[v])]; r[0]+=1; r[1]+=int(any(fam)); r[2]=min(r[2],sum(fam)); r[3]=min(r[3],len(fam))
        if not any(fam): fails.append((key,v,P.copy()))
print("n=%d samples=%d time=%.0fs"%(n,cnt,time.time()-t0))
for k,(a,b,c,d) in sorted(res.items()):
    print("type",k[0],"deg(v)=%d:"%k[1],"cases",a,"star(v) extends to a net in",b,"| min #good in family",c,"family size >=",d)
if fails: np.save("conjC_fail_n%d.npy"%n,fails[0][2]); print("FAIL example saved",fails[0][:2])

import numpy as np, collections, sys
from unfold import Polytope
from gen import rand_points
rng = np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
def sig(p, cut):
    d = collections.Counter()
    for u,v in cut: d[u]+=1; d[v]+=1
    apex = [v for v in p.deg if p.deg[v]==3]; eq=[v for v in p.deg if p.deg[v]==4]
    neq = sum(1 for u,v in cut if u in eq and v in eq)
    return (tuple(sorted(d[v] for v in apex)), tuple(sorted(d[v] for v in eq)), neq)
tot=collections.Counter(); bad=collections.Counter(); minclass=collections.defaultdict(lambda:10**9)
allgood_always=collections.Counter()
cnt=0
for it in range(N):
    P=rand_points(5,rng)
    try: p=Polytope(P)
    except: continue
    if len(p.faces)!=6: continue
    cnt+=1
    pen=p.penetrations()
    per=collections.defaultdict(lambda:[0,0])
    for t,pe in zip(p.trees(),pen):
        s=sig(p,p.cut_set(t)); tot[s]+=1; per[s][0]+=1
        if pe>0: bad[s]+=1; per[s][1]+=1
    for s,(a,b) in per.items():
        minclass[s]=min(minclass[s], a-b)
        if b==0: allgood_always[s]+=1
print("samples",cnt)
for s in sorted(tot):
    print(s, "trees/polytope", tot[s]//cnt, "bad frac %.3f"%(bad[s]/tot[s]), "min #good in class", minclass[s], "class fully good in %.3f of samples"%(allgood_always[s]/cnt))

import numpy as np, collections, sys, itertools, time
from unfold import Polytope
from gen import rand_points
n=int(sys.argv[1]); rng=np.random.default_rng(int(sys.argv[2])); N=int(sys.argv[3])

def automorphisms(n, edges):
    E=set(edges); auts=[]
    for perm in itertools.permutations(range(n)):
        if all(((perm[u],perm[v]) in E or (perm[v],perm[u]) in E) for u,v in edges):
            auts.append(perm)
    return auts
def canon(cut, auts):
    best=None
    for perm in auts:
        s=tuple(sorted(tuple(sorted((perm[u],perm[v]))) for u,v in cut))
        if best is None or s<best: best=s
    return best

# per combinatorial type (keyed by canonical edge set) keep stats
types={}
t0=time.time(); cnt=0
while cnt<N:
    P=rand_points(n,rng)
    try: p=Polytope(P)
    except: continue
    if len(p.P)!=n or len(p.faces)!=2*n-4: continue
    key=tuple(sorted(p.deg.values()))
    if key not in types:
        auts=automorphisms(n,p.edges)
        types[key]={'auts':auts,'ref_edges':p.edges,'classes':{},'samples':0,'mingood':10**9,'worstP':None}
    T=types[key]
    # map this polytope's graph onto the reference graph (find an isomorphism)
    ref=set(T['ref_edges']); iso=None
    for perm in itertools.permutations(range(n)):
        if all(((perm[u],perm[v]) in ref or (perm[v],perm[u]) in ref) for u,v in p.edges): iso=perm; break
    cnt+=1; T['samples']+=1
    pen=p.penetrations(); good=(pen<=0)
    if good.sum()<T['mingood']: T['mingood']=int(good.sum()); T['worstP']=P.copy()
    per=collections.defaultdict(lambda:[0,0])
    for t,g in zip(p.trees(),good):
        cut=[(iso[u],iso[v]) for u,v in p.cut_set(t)]
        c=canon(cut,T['auts']); per[c][0]+=1; per[c][1]+=int(g)
    for c,(a,b) in per.items():
        C=T['classes'].setdefault(c,{'size':a,'min_good':10**9,'sum_bad':0,'has_good':0})
        C['min_good']=min(C['min_good'],b); C['sum_bad']+=a-b; C['has_good']+=int(b>0)
print("n=%d samples=%d time=%.0fs"%(n,cnt,time.time()-t0))
for key,T in types.items():
    print("TYPE degrees",key,"samples",T['samples'],"trees",sum(C['size'] for C in T['classes'].values()),
          "classes",len(T['classes']),"min #good trees",T['mingood'])
    np.save("worst_n%d_%s.npy"%(n,''.join(map(str,key))),T['worstP'])
    rows=sorted(T['classes'].items(), key=lambda kv:(-kv[1]['has_good'],kv[1]['sum_bad']))
    for c,C in rows[:12]:
        print("   class size %2d  always-has-good-tree %.4f  class-all-good %s  bad-frac %.3f  cut=%s"%(
            C['size'],C['has_good']/T['samples'],'YES' if C['min_good']==C['size'] else 'no',
            C['sum_bad']/(C['size']*T['samples']),c))
